module Experiment

import Control.Monad.Writer
import Control.Monad.Identity
import Data.Vect
import Data.Nat
import Data.SnocList
import Data.SnocVect
import Data.SortedMap
import Decidable.Equality
import Language.Reflection
import Language.Reflection.Syntax

import Data.FinBitSet

%language ElabReflection

record UnificationTask where
  constructor MkUnificationTask
  lfv : Nat
  lhsFreeVars : Vect lfv (Name, TTImp)
  lhs : TTImp
  rfv : Nat
  rhsFreeVars : Vect rfv (Name, TTImp)
  rhs : TTImp

record DependencyGraph where
  constructor MkDG
  freeVars : Nat
  fvData : Vect freeVars (String, Name, TTImp, Maybe TTImp)
  fvDeps : Vect freeVars $ FinBitSet freeVars
  empties : FinBitSet freeVars
  nameToId : SortedMap Name $ Fin freeVars
  holeToId : SortedMap String $ Fin freeVars

Eq DependencyGraph where
  (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') with (decEq a a') 
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | Yes p =
    a == a' && b == (rewrite p in b') && c == (rewrite p in c') && 
      d == (rewrite p in d') && e == (rewrite p in e') && f == (rewrite p in f')
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | No _ = False

Show DependencyGraph where
  show (MkDG a b c d e f) = "MkDG \{show a} \{show b} \{show c} \{show d} \{show e} \{show f}"

genNameToId : 
  {freeVars : Nat} -> 
  Vect freeVars (String, Name, TTImp, Maybe TTImp) -> 
  SortedMap Name $ Fin freeVars
genNameToId fvs = 
  foldl (\acc, (f, _, n, _) => insert n f acc) empty (zip (allFins freeVars) fvs)

genHoleToId : 
  {freeVars : Nat} -> 
  Vect freeVars (String, Name, TTImp, Maybe TTImp) -> 
  SortedMap String $ Fin freeVars
genHoleToId fvs = 
  foldl (\acc, (f, s, _) => insert s f acc) empty (zip (allFins freeVars) fvs)

aMHImpl : 
  {0 freeVars : Nat} ->
  MonadWriter (FinBitSet freeVars) m =>
  SortedMap String (Fin freeVars) ->
  TTImp ->
  m TTImp
aMHImpl h2Id h@(IHole _ s) = 
  case (lookup s h2Id) of
       Just id => writer (h, insert id empty)
       Nothing => pure h
aMHImpl _ t = pure t

allMatchingHoles :
  {0 freeVars : Nat} ->
  SortedMap String (Fin freeVars) ->
  TTImp ->
  FinBitSet freeVars
allMatchingHoles h2Id t = execWriter $ mapMTTImp (aMHImpl h2Id) t

genDeps : 
  {freeVars : Nat} ->
  Vect freeVars (String, Name, TTImp, Maybe TTImp) ->
  SortedMap String (Fin freeVars) ->
  Vect freeVars $ FinBitSet freeVars
genDeps fvs h2Id = 
  map 
    (\(s,n,ty,val) => 
      merge (allMatchingHoles h2Id ty) $ 
        fromMaybe empty $ 
          allMatchingHoles h2Id <$> val)
    fvs

genEmpties : 
  {freeVars : Nat} ->
  Vect freeVars (String, Name, TTImp, Maybe TTImp) -> 
  FinBitSet freeVars
genEmpties fvs = genEmpties' empty $ zip (allFins freeVars) fvs
  where
    genEmpties' : FinBitSet fv -> Vect _ (Fin fv, String, Name, TTImp, Maybe TTImp) -> FinBitSet fv
    genEmpties' set [] = set
    genEmpties' set ((_, _, _, _, Just _) :: xs) = genEmpties' set xs
    genEmpties' set ((f, _, _, _, Nothing) :: xs) = genEmpties' (insert f set) xs

genDG : 
  {freeVars : Nat} -> 
  Vect freeVars (String, Name, TTImp, Maybe TTImp) -> 
  DependencyGraph
genDG fvs = do
  let h2Id = genHoleToId fvs
  MkDG freeVars fvs (genDeps fvs h2Id) (genEmpties fvs) (genNameToId fvs) h2Id

canSub : 
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars
canSub dg = 
  removeAll dg.empties $ 
    foldl 
      (\s, (i, n) => 
        if (removeAll dg.empties n) == empty 
           then insert i s 
           else s) 
      empty $ 
        zip (allFins dg.freeVars) dg.fvDeps

subMatchingHolesImpl :
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars ->
  TTImp -> 
  TTImp
subMatchingHolesImpl dg fbs ih@(IHole _ h) = 
  case lookup h dg.holeToId of
    Just id => 
      if lookup id fbs 
        then 
          let (_, _, _, x) = index id dg.fvData 
          in fromMaybe ih x
        else ih
    Nothing => ih
subMatchingHolesImpl _ _ t = t

subMatchingHoles :
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars ->
  TTImp -> 
  TTImp
subMatchingHoles dg fbs = mapTTImp (subMatchingHolesImpl dg fbs)

updateData : 
  (dg: DependencyGraph) -> 
  FinBitSet dg.freeVars -> 
  (String, (Name, (TTImp, Maybe TTImp))) -> 
  (String, (Name, (TTImp, Maybe TTImp)))
updateData dg canSub (s,n,t,mv) = 
  (s,n, subMatchingHoles dg canSub t, subMatchingHoles dg canSub <$> mv)

doSub : 
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars ->
  DependencyGraph
doSub dg canSub = 
  { fvData $= map (updateData dg canSub)
  , fvDeps $= map (removeAll canSub)
  } dg

subEmptiesTImpl : (dg : DependencyGraph) -> TTImp -> TTImp
subEmptiesTImpl dg t@(IHole _ h) = do
  let Just id = lookup h dg.holeToId
  | _ => t
  if lookup id dg.empties
    then 
      let (_, x, _, _) = index id dg.fvData 
      in IVar EmptyFC x
    else t
subEmptiesTImpl dg t = t

subEmptiesT : DependencyGraph -> TTImp -> TTImp
subEmptiesT dg = mapTTImp (subEmptiesTImpl dg)

updateDataE : 
  (dg: DependencyGraph) -> 
  (String, (Name, (TTImp, Maybe TTImp))) -> 
  (String, (Name, (TTImp, Maybe TTImp)))
updateDataE dg (s,n,t,mv) = 
  (s,n, subEmptiesT dg t, subEmptiesT dg <$> mv)

subEmpties :
  (dg : DependencyGraph) ->
  DependencyGraph
subEmpties dg = {fvData $= map (updateDataE dg)} dg

solveDG : 
  (dg : DependencyGraph) ->
  DependencyGraph
solveDG dg = do
  let cs = canSub dg
  let False = cs == empty
  | _ => dg
  let ds = doSub dg cs
  if ds == dg 
     then dg 
     else solveDG $ doSub dg cs

record UnificationResult where
  constructor MkUnificationResult
  lhsResult : SortedMap Name $ Maybe TTImp
  rhsResult : SortedMap Name $ Maybe TTImp
  fords : List (TTImp, TTImp)

genHoleNames : 
  SnocVect l (Name, TTImp) -> Elab $ (SortedMap Name String, SnocVect l String)
genHoleNames [<] = pure (empty, [<])
genHoleNames (xs :< (n, _)) = do
  gs <- genSym $ show n
  (others, others') <- genHoleNames xs
  pure $ (insert n (show gs) others, others' :< show gs)

buildUpDPair : SnocVect l (Name, TTImp) -> TTImp -> TTImp
buildUpDPair [<] t = t
buildUpDPair (xs :< (n, ty)) t = 
  buildUpDPair xs 
    `(Builtin.DPair.DPair ~ty ~(ILam EmptyFC MW ExplicitArg (Just n) ty t))

buildUpTarget : SnocVect l (String, Name, TTImp) -> TTImp -> TTImp
buildUpTarget [<] t = t
buildUpTarget (xs :< (s, n, _)) t = 
  buildUpTarget xs `((~(IHole EmptyFC s) ** ~t))

extractFVData : (t : Type) -> t -> Vect l (Name, TTImp) -> Vect l String -> Elab $ Vect l (Name, TTImp, Maybe TTImp)
extractFVData t v ((n, t') :: xs) (hn :: hns) = do
  case t of
    (DPair myTy dNext) => do
      let (vv ** vRest) = v
      quoteV <- quote vv
      quoteT <- quote myTy
      logMsg "" 0 "\{show n} : \{show quoteT} = \{show quoteV}"
      rest <- extractFVData (dNext vv) vRest xs hns
      let retVal = case quoteV of IHole _ hh => if hh == hn then Nothing else Just quoteV; qv => Just qv
      pure $ (n, quoteT, retVal) :: rest
    _ => do
      qT <- quote t
      fail "Failed to extract dependent pair from \{show qT}" 
extractFVData _ _ [] [] = pure []

unify : UnificationTask -> Elab $ Either String UnificationResult
unify task = do
  let allFreeVars = task.lhsFreeVars ++ task.rhsFreeVars
  let snocLFV = fromVect task.lhsFreeVars
  let snocRFV = fromVect task.rhsFreeVars
  (lhsNMap, lhsNames) <- genHoleNames snocLFV
  (rhsNMap, rhsNames) <- genHoleNames snocRFV
  let allNames = lhsNames ++ rhsNames
  -- Assemble the type, the value of which is all our free variables + proof of equality
  let checkTargetType = 
    buildUpDPair snocLFV $ 
      buildUpDPair snocRFV `(~(task.lhs) ~=~ ~(task.rhs))
  -- Assemble the value (holes + Refl)
  let checkTarget = 
    buildUpTarget (zip lhsNames snocLFV) $ 
      buildUpTarget (zip rhsNames snocRFV) `(Refl)
  logMsg "" 0 "\{show checkTargetType}"
  logMsg "" 0 "\{show checkTarget}"
  -- Instantiate target type
  checkTargetType' : Type <- check checkTargetType
  -- Run unification
  checkTarget' : checkTargetType' <- check checkTarget
  ctQuote <- quote checkTarget'
  logMsg "" 0 "\{show ctQuote}"
  let vectNames = toVect allNames
  -- Extract unification results
  uniResults <- extractFVData checkTargetType' checkTarget' allFreeVars vectNames
  -- Generate dependency graph
  let dg = genDG $ zip vectNames uniResults
  logMsg "" 0 "\{show dg}"
  let dg = subEmpties dg
  logMsg "" 0 "Subst empties: \{show dg}"
  let solved = solveDG dg
  logMsg "" 0 "Solved DG : \{show solved}"
  pure $ Left ""
