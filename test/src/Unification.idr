module Unification

import public Language.Reflection.Unification3
import public Language.Reflection.Unification3.Convert

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

artInner : GlobalVars -> SnocList (Name, TTImp) -> TTImp -> TTImp -> EitherT UnificationError (WriterT (List String) Identity) TTImp
artInner gv freeVars from to = do
  fv <- convertFreeVars freeVars
  from' <- convertToIR fv [<] from
  let cb = baseConstraints (length freeVars) 0
  evalStateT cb $ do
    reduced <- 
      reduce @{%search} @{%search} @{logWriter} {bds = MKBounds (length freeVars) 0} gv True fv BoundVars.Lin from'

    logStr @{logWriter} 0 "result = \{show reduced}"

    pure $ convertFromIR fv [<] reduced

-- Reduction
assertReducesTo : Monad m => GlobalVars -> SnocList (Name, TTImp) -> TTImp -> TTImp -> TestT m ()
assertReducesTo gv freeVars from to = do
  let (res, logs) = runIdentity $ runWriterT $ runEitherT $ artInner gv freeVars from to

  footnote $ joinBy "\n" logs
  -- traverse_ (\x => footnote x) logs

  res <- evalEither res

  res === to

reducesTo : {default [<] fvs : SnocList (Name, TTImp)} -> TTImp -> TTImp -> Property
reducesTo {fvs} from to = property1 $ assertReducesTo (mockGV [`{S}, `{Z}, `{Nat}]) fvs from to

public export
reductions : Group
reductions = MkGroup "IR Reduction tests"
  [ ("Global variables don't reduce", `(Nat) `reducesTo` `(Nat))
  , ("Free variables don't reduce", reducesTo {fvs = [< (`{x}, `(Nat))]} `(x) `(x))
  , ("(\\x=>S x) x -> S x", `((\x: Nat => S x) Z) `reducesTo` `(S Z))
  , ("(\\x,y=>x+y) 1 2 -> 1 + 2", `((\x: Nat, y: Nat => x+y) (S Z) Z) `reducesTo` `((S Z) + Z))
  -- -- TODO: this should actually be rejected!
  -- , ("(\\x,y=>x+y) {x=1} 2 -> 1 + 2", `((\x: Nat, y: Nat => x+y) {x=S Z} Z) `reducesTo` `((S Z) + Z))
  , ("(\\x,y=>x+y) 1 {y=2} -> 1 + 2", `((\x: Nat, y: Nat => x+y) (S Z) {y=Z}) `reducesTo` `((S Z) + Z))
  , ("(\\x,y=>x+y) {x=1} {y=2} -> 1 + 2", `((\x: Nat, y: Nat => x+y) {x=S Z} {y=Z}) `reducesTo` `((S Z) + Z))
  , ("(\\x,y=>x+y) {y=2} {x=1} -> 1 + 2", `((\x: Nat, y: Nat => x+y) {y=Z} {x=S Z}) `reducesTo` `((S Z) + Z))
  , ("let x=Z in S x -> S Z", `(let x : Nat = Z in S x) `reducesTo` `(S Z))
  , ( "higher order functions 1"
    , `((\x : ((x : Nat) -> Nat), y: Nat => x y) (\x : Nat => S (S x)) Z) `reducesTo` `(S (S Z)))
  ]
