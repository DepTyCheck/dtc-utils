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


-- Reduction
assertReducesTo : Monad m => GlobalVars -> SnocList (Name, TTImp) -> TTImp -> TTImp -> TestT m ()
assertReducesTo gv freeVars from to = do
  res <- evalEither {x=UnificationError} $ do
    fvs <- convertFreeVars freeVars
    from' <- convertToIR fvs [<] from
    let cb = baseConstraints (length freeVars) 0
    evalStateT {m=Either UnificationError} cb $ do
      reduced <- reduce gv True (fvs, BoundVars.Lin, from')
      pure $ convertFromIR fvs [<] reduced

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
  ]
