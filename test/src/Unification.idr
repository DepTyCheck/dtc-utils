module Unification

import public Language.Reflection.Unifier.ManualUnifier
import public Language.Reflection.Unifier.ManualUnifier.Convert

import public Data.Either
import public Control.Monad.State
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Control.Monad.Either
import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.Writer
import public Control.Monad.Identity

import public Hedgehog

%language ElabReflection

assertConvertsTo : Monad m => TTImp -> FreeVars vs -> IRTerm vs 0 -> TestT m ()
assertConvertsTo t fv expected = do
  res <- evalEither {x=UnificationError} $ convertToIR fv [<] t
  res === expected

assertConvertFails : Monad m => TTImp -> FreeVars vs -> TestT m ()
assertConvertFails t fv =
  assert $ isLeft {a=UnificationError} $ convertToIR fv [<] t

typeConverts : Property
typeConverts = property1 $ do
  assertConvertsTo `(Type) [<] IRType

primConverts : Property
primConverts = property1 $ do
  assertConvertsTo (IPrimVal EmptyFC (I 10)) [<] (IRPrim (I 10)) 

fvConverts : Property
fvConverts = property1 $ do
  assertConvertsTo `(x) [< (`{x}, IRType)] $ IRFreeVar 0

lambdaConverts : Property
lambdaConverts = property1 $ do
  assertConvertsTo `(\x:Nat => S x) [<] $ 
    IRLam MW ExplicitArg `{x} (IRGlobalVar `{Nat}) $ 
      IRApp (IRGlobalVar `{S}) (IRLocalVar 0)

letConverts : Property
letConverts = property1 $ do
  assertConvertsTo `(let x : Nat = Z in S x) [<] $
    IRLet MW `{x} (IRGlobalVar `{Nat}) (IRGlobalVar `{Z}) $
      IRApp (IRGlobalVar `{S}) (IRLocalVar 0)
  
letShadows : Property
letShadows = property1 $ do
  assertConvertsTo `(let x : Nat = Z in S x) [< (`{x}, IRGlobalVar `{Nat})] $
    IRLet MW `{x} (IRGlobalVar `{Nat}) (IRGlobalVar `{Z}) $
      IRApp (IRGlobalVar `{S}) (IRLocalVar 0)

public export
singleConversions : Group
singleConversions = MkGroup "Conversion of minimal expressions" 
  [ ("IType -> IRType", typeConverts)
  , ("IPrimVal -> IRPrim", primConverts)
  , ("IVar -> IRFreeVar", fvConverts)
  , ("ILam -> IRLam", lambdaConverts)
  , ("ILet -> ILet", letConverts)
  , ("ILet shadowing free variables", letShadows)
  ]

runReduction : 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  EitherT UnificationError (WriterT (List String) Identity) TTImp
runReduction gv freeVars from = do
  fv <- convertFreeVars freeVars
  from' <- convertToIR fv [<] from
  let cb = baseConstraints $ MkBounds (length freeVars) 0
  evalStateT cb $ do
    reduced <- 
      reduce @{%search} @{%search} @{logWriter} {bds = MkBounds (length freeVars) 0} gv (MkAFV fv [<]) True BoundVars.Lin from'

    logStr @{logWriter} 0 "result = \{show reduced}"

    pure $ convertFromIR fv [<] reduced

assertReturns : 
  Monad m =>
  Eq t =>
  Show t =>
  EitherT UnificationError (WriterT (List String) Identity) t ->
  t ->
  TestT m ()
assertReturns a b = do
  let (res, logs) = runIdentity $ runWriterT $ runEitherT $ a
  footnote $ joinBy "\n" logs
  res <- evalEither res
  res === b

assertFails : 
  Monad m =>
  Show t =>
  EitherT UnificationError (WriterT (List String) Identity) t ->
  UnificationError ->
  TestT m ()
assertFails a b = do
  let (res, logs) = runWriter $ runEitherT $ a
  footnote $ joinBy "\n" logs
  diff res (\a,_=>isLeft a) b

-- -- Reduction
assertReducesTo : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  TTImp -> 
  TestT m ()
assertReducesTo gv freeVars from to = do
  flip assertReturns to $ runReduction gv freeVars from

assertReduceFails : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  UnificationError -> 
  TestT m ()
assertReduceFails gv fv from to = do
  flip assertFails to $ runReduction gv fv from

mockGlobals = mockGV [`{S}, `{Z}, `{Nat}, "List"]

reducesTo : {default [<] fvs : SnocList (Name, TTImp)} -> TTImp -> TTImp -> Property
reducesTo {fvs} from to = property1 $ assertReducesTo mockGlobals fvs from to

reduceFails : {default [<] fvs : SnocList (Name, TTImp)} -> TTImp -> UnificationError -> Property
reduceFails {fvs} from to = property1 $ assertReduceFails mockGlobals fvs from to

runTypeof : 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  EitherT UnificationError (WriterT (List String) Identity) TTImp
runTypeof gv freeVars from = do
  fv <- convertFreeVars freeVars
  from' <- convertToIR fv [<] from
  let cb = baseConstraints $ MkBounds (length freeVars) 0
  evalStateT cb $ do
    reduced <- 
      typeof @{%search} @{%search} @{logWriter} {bds = MkBounds (length freeVars) 0} gv (MkAFV fv [<]) True BoundVars.Lin from'

    logStr @{logWriter} 0 "result = \{show reduced}"

    pure $ convertFromIR fv [<] reduced

assertTypeofIs : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  TTImp -> 
  TestT m ()
assertTypeofIs gv freeVars from to = do
  flip assertReturns to $ runTypeof gv freeVars from

assertTypeofFails : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  UnificationError -> 
  TestT m ()
assertTypeofFails gv fv from to = do
  flip assertFails to $ runTypeof gv fv from

typeofIs : {default [<] fvs : SnocList (Name, TTImp)} -> TTImp -> TTImp -> Property
typeofIs {fvs} from to = property1 $ assertTypeofIs mockGlobals fvs from to

typeofFails : {default [<] fvs : SnocList (Name, TTImp)} -> TTImp -> UnificationError -> Property
typeofFails {fvs} from to = property1 $ assertReduceFails mockGlobals fvs from to

runUnify : 
  GlobalVars ->  
  SnocList (Name, TTImp) -> 
  TTImp -> 
  SnocList (Name, TTImp) -> 
  TTImp ->
  EitherT UnificationError (WriterT (List String) Identity) 
    (b : Bounds ** (FreeVars b.fvsL, FreeVars b.fvsR, Constraints b))
runUnify gv fvL lhs fvR rhs = do
  fvL' <- convertFreeVars fvL
  lhs' <- convertToIR fvL' [<] lhs
  fvR' <- convertFreeVars fvR
  rhs' <- convertToIR fvR' [<] rhs
  let cb = baseConstraints $ MkBounds (length fvL) (length fvR)
  (newState, _) <- runStateT {m = EitherT UnificationError (WriterT (List String) Identity)} cb $ do
    unify 
      @{%search} @{%search} @{logWriter} 
      {bds = MkBounds (length fvL) (length fvR)} 
      gv (MkAFV fvL' fvR') True [<] lhs' False [<] rhs'
  pure (MkBounds (length fvL) (length fvR) ** (fvL', fvR', newState))

allSameAs : Eq t => t -> List t -> Bool
allSameAs x [] = True
allSameAs x (a :: as) = x == a && allSameAs x as

allSame : Eq t => List t -> Bool
allSame [] = True
allSame [x] = True
allSame (x :: xs) = allSameAs x xs

hasBucket : 
  List Name -> 
  List Name -> 
  Maybe (Bool, TTImp) -> 
  (b : Bounds ** (FreeVars b.fvsL, FreeVars b.fvsR, Constraints b)) -> 
  Bool
hasBucket ls rs val (b ** (fvL, fvR, constraints)) = do
  let Just ls' = traverse (flip queryFV fvL) ls
  | _ => False
  let Just rs' = traverse (flip queryFV fvR) rs
  | _ => False
  let lsBkt = map (\x => bIndexOf True x constraints) ls'
  let rsBkt = map (\x => bIndexOf False x constraints) rs'
  let True = allSame $ lsBkt ++ rsBkt
  | _ => False
  let (bIndex :: _) = lsBkt ++ rsBkt
  | _ => True
  let bucket = index bIndex constraints.bucketData
  let True = FinBitSet.fromList ls' == bucket.membersL && FinBitSet.fromList rs' == bucket.membersR
  | _ => False
  case val of
    Just (True, val) => do
      let Just (True ** bucketVal) = bucket.equalsTo
      | _ => False
      convertFromIR fvL [<] bucketVal == val
    Just (False, val) => do
      let Just (False ** bucketVal) = bucket.equalsTo
      | _ => False
      convertFromIR fvR [<] bucketVal == val     
    Nothing => isNothing bucket.equalsTo

hasBuckets : 
  List (List Name, List Name, Maybe (Bool, TTImp)) -> 
  (b : Bounds ** (FreeVars b.fvsL, FreeVars b.fvsR, Constraints b)) -> 
  Bool
hasBuckets [] _ = True
hasBuckets ((a,b,c) :: xs) st = hasBucket a b c st && hasBuckets xs st

assertUnifiesTo : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  List (List Name, List Name, Maybe (Bool, TTImp)) ->
  TestT m ()
assertUnifiesTo gv fvL lhs fvR rhs buckets = do
  let (result, logs) = runIdentity $ runWriterT $ runEitherT $ runUnify gv fvL lhs fvR rhs
  footnote $ joinBy "\n" logs
  constraints <- evalEither result
  footnote $ "State: \{show constraints}"
  assert $ hasBuckets buckets constraints

assertUnifyFails : 
  Monad m => 
  GlobalVars -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  UnificationError ->
  TestT m ()
assertUnifyFails gv fvL lhs fvR rhs err = do
  flip assertFails err $ runUnify gv fvL lhs fvR rhs

unifiesTo : 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  List (List Name, List Name, Maybe (Bool, TTImp)) ->
  Property
unifiesTo fvL lhs fvR rhs buckets = 
  property1 $ assertUnifiesTo mockGlobals fvL lhs fvR rhs buckets

unifyFails : 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  SnocList (Name, TTImp) -> 
  TTImp -> 
  UnificationError ->
  Property
unifyFails fvL lhs fvR rhs err = 
  property1 $ assertUnifyFails mockGlobals fvL lhs fvR rhs err

public export
reductions : Group
reductions = MkGroup "IR Reduction tests"
  [ ("Global variables don't reduce", `(Nat) `reducesTo` `(Nat))
  , ("Free variables don't reduce", reducesTo {fvs = [< (`{x}, `(Nat))]} `(x) `(x))
  , ("(\\x=>S x) x -> S x", `((\x: Nat => S x) Z) `reducesTo` `(S Z))
  , ( "(\\x,y=>x+y) 1 2 -> 1 + 2"
    , `((\x: Nat, y: Nat => x+y) (S Z) Z) `reducesTo` `((S Z) + Z))
  , ( "(\\x,y=>x+y) {x=1} 2 fails"
    , `((\x: Nat, y: Nat => x+y) {x=S Z} Z) `reduceFails` AppNameNotFoundError "x")
  , ( "(\\x,y=>x+y) 1 {y=2} -> 1 + 2"
    , `((\x: Nat, y: Nat => x+y) (S Z) {y=Z}) `reducesTo` `((S Z) + Z))
  , ( "(\\x,y=>x+y) {x=1} {y=2} -> 1 + 2"
    , `((\x: Nat, y: Nat => x+y) {x=S Z} {y=Z}) `reducesTo` `((S Z) + Z))
  , ( "(\\x,y=>x+y) {y=2} {x=1} -> 1 + 2"
    , `((\x: Nat, y: Nat => x+y) {y=Z} {x=S Z}) `reducesTo` `((S Z) + Z))
  , ("let x=Z in S x -> S Z", `(let x : Nat = Z in S x) `reducesTo` `(S Z))
  , ( "higher order functions 1"
    , `((\x : ((x : Nat) -> Nat), y: Nat => x y) (\x : Nat => S (S x)) Z) `reducesTo` `(S (S Z)))
  , ( "higher order functions 2"
    , `((\x : ((x : Nat) -> Nat), y: Nat => x y) S Z) `reducesTo` `(S  Z))
  , ("1=1", `(S Z) `reducesTo` `(S Z))
  , ("Vect l t", reducesTo {fvs=[<("l", `(Nat))]} `(Vect l Nat) `(Vect l Nat))
  , ("Big functions", `((\x : Nat, y : Nat, z : Nat => x + y + z) Z Z Z) `reducesTo` `(Z + Z + Z))
  , ("Partial application", `((\x : Nat, y : Nat, z : Nat => x + y + z) Z) `reducesTo` `((\y : Nat, z : Nat => Z + y + z))) 
  ]

public export
typeofs : Group
typeofs = MkGroup "IR Typeof tests"
  [ ("Global variable typeof", `(Nat) `typeofIs` `(Type))
  , ("Free variable typeof", typeofIs {fvs=[<("x", `(Nat))]} `(x) `(Nat))
  , ("Local variable typeof", typeofIs `(let x : Nat = Z in x) `(Prelude.Types.Nat))
  , ("Application (with globals)", `(S Z) `typeofIs` `(Prelude.Types.Nat))
  , ("Application (with lambda)", `((\x: Nat => S x) Z) `typeofIs` `(Prelude.Types.Nat))
  , ("Generic type", `(List Nat) `typeofIs` `(Type))
  , ("Partial application", typeofIs {fvs=[<("vect", `((len : Nat) -> (elem : Type) -> Type))]} `(vect (S Z)) `((elem : Type) -> Type))
  , ("Lambda over fn", typeofIs {fvs=[<("vect", `((len : Nat) -> (elem : Type) -> Type))]} `((\x : Nat => vect x Nat)) `((x : Nat) -> Type))
  ]

public export
unifys : Group
unifys = MkGroup "IR unification tests"
  [ ("Free var = Global var", 
      unifiesTo [<("x", `(Type))] `(x) [<] `(Nat) [(["x"], [], Just (False, `(Nat)))])
  , ("Free var = Free var", 
      unifiesTo [<("x", `(Type))] `(x) [< ("y", `(Type))] `(y) [(["x"], ["y"], Nothing)])
  , ("GV = GV", unifiesTo [<] `(Z) [<] `(Z) [])
  , ("identical IRApp", unifiesTo [<] `(S Z) [<] `(S Z) [])
  , ("basic lambdas equal", unifiesTo [<] `(\x : Nat => x) [<] `(\x : Nat => x) []) 
  , ("basic lambda different", unifyFails [<] `(\x, y : Nat => x) [<] `(\x,y : Nat => y) (NEVarsError "x" "y")) 
  , ("identical pis", unifiesTo [<] `((x, y : Type) -> x) [<] `((x, y : Type) -> x) [])
  , ("different pis", unifyFails [<] `((x, y : Type) -> x) [<] `((x, y : Type) -> y) (NEVarsError "x" "y"))
  , ("crossing-over fn invocations",
      unifiesTo 
        [<("Vect", `((len : Nat) -> (elem : Type) -> Type)), ("x", `(Nat))] `(Vect x Nat)
        [<("Vect", `((len : Nat) -> (elem : Type) -> Type)), ("y", `(Type))] `(Vect (S Z) y)
        [   (["Vect"],["Vect"], Nothing)
          , (["x"], [], Just (False, `(S Z)))
          , ([], ["y"], Just (True, `(Nat)))
          ])
  ]
