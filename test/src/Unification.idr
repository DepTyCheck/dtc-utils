module Unification

import Language.Reflection.Unification3

import Data.Either
import Language.Reflection.TTImp

import Hedgehog

-- Conversion

assertConvertsTo : Monad m => TTImp -> FreeVars vs -> IRTerm vs 0 -> TestT m ()
assertConvertsTo t fv expected = do
  res <- evalEither $ convertToIR {m=Either UnificationError} fv [<] t
  res === expected

assertConvertFails : Monad m => TTImp -> FreeVars vs -> TestT m ()
assertConvertFails t fv =
  assert $ isLeft $ convertToIR {m=Either UnificationError} fv [<] t

typeConverts : Property
typeConverts = property1 $ do
  assertConvertsTo `(Type) [<] IRType

primConverts : Property
primConverts = property1 $ do
  traverse_ (\x => assertConvertsTo (IPrimVal EmptyFC x) [<] (IRPrim x))
    [I 10]

fvConverts : Property
fvConverts = property1 $ do
  assertConvertsTo `(x) [< (`{x}, IRType)] $ IRFreeVar 0
  
public export
singleConversions : Group
singleConversions = MkGroup "Conversion of minimal expressions" 
  [ ("IType -> IRType", typeConverts)
  , ("IPrimVal -> IRPrim", primConverts)
  , ("IVar -> IRFreeVar", fvConverts)
  ]
