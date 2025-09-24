module Language.Reflection.Unifier.TypecheckUnifier

import public Control.Monad.Writer
import public Control.Monad.Identity
import public Data.SnocVect

import public Language.Reflection.Unifier.Interface

genNameToId : 
  {freeVars : Nat} -> 
  Vect freeVars FVData -> 
  SortedMap Name $ Fin freeVars
genNameToId fvs = 
  foldl (\acc, (i, fv) => insert fv.name i acc) empty (zip (allFins freeVars) fvs)

genHoleToId : 
  {freeVars : Nat} -> 
  Vect freeVars FVData -> 
  SortedMap String $ Fin freeVars
genHoleToId fvs = 
  foldl (\acc, (i, fv) => insert fv.holeName i acc) empty (zip (allFins freeVars) fvs)

aMHImpl : 
  {0 freeVars : Nat} ->
  MonadWriter (FinBitSet freeVars) m =>
  SortedMap String (Fin freeVars) ->
  TTImp ->
  m TTImp
aMHImpl h2Id h = do
  let (IHole _ s) = h
  | _ => pure h
  let (Just id) = lookup s h2Id
  | _ => pure h
  writer (h, insert id empty)

allMatchingHoles :
  {0 freeVars : Nat} ->
  SortedMap String (Fin freeVars) ->
  TTImp ->
  FinBitSet freeVars
allMatchingHoles h2Id t = execWriter $ mapMTTImp (aMHImpl h2Id) t

genDeps : 
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  SortedMap String (Fin freeVars) ->
  Vect freeVars $ FinBitSet freeVars
genDeps fvs h2Id = 
  map 
    (\fv => 
      merge (allMatchingHoles h2Id fv.type) $ 
        fromMaybe empty $ 
          allMatchingHoles h2Id <$> fv.value)
    fvs

genEmpties : 
  {freeVars : Nat} ->
  Vect freeVars FVData -> 
  FinBitSet freeVars
genEmpties fvs = foldl genEmpties' empty $ zip (allFins freeVars) fvs
  where
    genEmpties' : FinBitSet fv -> (Fin fv, FVData) -> FinBitSet fv
    genEmpties' set (i, fv) = 
      if isNothing fv.value 
         then set 
         else insert i set

genDG : 
  {freeVars : Nat} -> 
  Vect freeVars FVData -> 
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
      empty 
      $ zip (allFins dg.freeVars) dg.fvDeps

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
          let fv = index id dg.fvData 
          in fromMaybe ih fv.value
        else ih
    Nothing => ih
subMatchingHolesImpl _ _ t = t

subMatchingHoles :
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars ->
  TTImp -> 
  TTImp
subMatchingHoles dg fbs = mapTTImp $ subMatchingHolesImpl dg fbs

fvSubMatching : 
  (dg: DependencyGraph) -> 
  FinBitSet dg.freeVars -> 
  FVData -> 
  FVData
fvSubMatching dg canSub = 
  { type $= subMatchingHoles dg canSub
  , value $= map $ subMatchingHoles dg canSub
  }

doSub : 
  (dg : DependencyGraph) ->
  FinBitSet dg.freeVars ->
  DependencyGraph
doSub dg canSub = 
  { fvData $= map $ fvSubMatching dg canSub
  , fvDeps $= map $ removeAll canSub
  } dg

subEmptiesTImpl : (dg : DependencyGraph) -> TTImp -> TTImp
subEmptiesTImpl dg t@(IHole _ h) = do
  let Just id = lookup h dg.holeToId
  | _ => t
  if lookup id dg.empties
    then 
      let fv = index id dg.fvData 
      in IVar EmptyFC fv.name
    else t
subEmptiesTImpl dg t = t

subEmptiesT : DependencyGraph -> TTImp -> TTImp
subEmptiesT dg = mapTTImp $ subEmptiesTImpl dg

subEmptiesFV : 
  (dg: DependencyGraph) -> 
  FVData -> 
  FVData
subEmptiesFV dg  = 
  { type $= subEmptiesT dg
  , value $= map $ subEmptiesT dg
  }

subEmpties :
  (dg : DependencyGraph) ->
  DependencyGraph
subEmpties dg = {fvData $= map $ subEmptiesFV dg} dg

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
     else solveDG ds

genHoleNames : 
  Elaboration m => 
  SnocVect l (Name, _) -> 
  m $ (SortedMap Name String, SnocVect l String)
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

extractFVData : 
  Elaboration m => 
  MonadError String m =>
  (t : Type) -> 
  t -> 
  Vect l (Name, TTImp) -> 
  Vect l String -> 
  m $ Vect l (Name, TTImp, Maybe TTImp)
extractFVData t v ((n, t') :: xs) (hn :: hns) = do
  case t of
    (DPair myTy dNext) => do
      let (vv ** vRest) = v
      quoteV <- quote vv
      quoteT <- quote myTy
      logMsg "Unifier.TypecheckUnifier" 0 "\{show n} : \{show quoteT} = \{show quoteV}"
      rest <- extractFVData (dNext vv) vRest xs hns
      let retVal = case quoteV of IHole _ hh => if hh == hn then Nothing else Just quoteV; qv => Just qv
      pure $ (n, quoteT, retVal) :: rest
    _ => do
      qT <- quote t
      throwError "Failed to extract dependent pair from \{show qT}" 
extractFVData _ _ [] [] = pure []

-- TODO: Crashes if given a task with named holes
unify : 
  Elaboration m => 
  MonadError String m => 
  UnificationTask -> 
  m $ DependencyGraph
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
  logMsg "Unifier.TypecheckUnifier" 0 "\{show checkTargetType}"
  logMsg "Unifier.TypecheckUnifier" 0 "\{show checkTarget}"
  -- Instantiate target type
  (Just checkTargetType') : Maybe Type <-
    try (Just <$> check checkTargetType) (pure Nothing)
  | _ => throwError "Failed to build target type (\{show checkTargetType})"
  -- Run unification
  (Just checkTarget') : Maybe checkTargetType' <- 
    try (Just <$> check checkTarget) (pure Nothing)
  | _ => throwError "Unification failed"
  ctQuote <- quote checkTarget'
  logMsg "Unifier.TypecheckUnifier" 0 "\{show ctQuote}"
  let vectNames = toVect allNames
  -- Extract unification results
  uniResults <- 
    extractFVData checkTargetType' checkTarget' allFreeVars vectNames
  -- Generate dependency graph
  let dg = genDG $ makeFVData <$> zip vectNames uniResults
  logMsg "Unifier.TypecheckUnifier" 0 "\{show dg}"
  let dg = subEmpties dg
  logMsg "Unifier.TypecheckUnifier" 0 "Subst empties: \{show dg}"
  let solved = solveDG dg
  logMsg "Unifier.TypecheckUnifier" 0 "Solved DG : \{show solved}"
  pure solved

public export
typeCheckUnifier : Unifier
typeCheckUnifier task = 
  try 
    (runEitherT {m=Elab} $ unify task) 
    (pure $ Left $ "Unification failed catastrophically (likely because of the named hole bug)")

