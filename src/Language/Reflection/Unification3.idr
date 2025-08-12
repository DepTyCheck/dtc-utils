module Language.Reflection.Unification3

import Language.Reflection.Unification3.IR

import Control.Monad.Error.Interface

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp

import Data.Fin
import Data.Nat
import Data.Vect
import Data.Vect.Views

||| List of free variables in expression
||| @ vs amount of free variables
data FreeVars : (vs : Nat) -> Type where
  Lin  : FreeVars 0
  (:<) : FreeVars vs -> (Name, IRTerm vs 0) -> FreeVars (S vs)

namespace FreeVars
  ||| Get a free variable's name and type by its de Bruijn index
  index : Fin vs -> FreeVars vs -> (Name, IRTerm vs 0)
  index FZ     (x :< (y, z)) = (y, raiseVs z)
  index (FS x) (y :< z)      = mapSnd raiseVs $ index x y

||| Find the index of a free varible by its name
queryFV : Name -> FreeVars vs -> Maybe $ Fin vs
queryFV nm [<] = Nothing
queryFV nm (xs :< (nm', x)) = if nm == nm' 
                                 then Just 0 
                                 else shift 1 <$> queryFV nm xs

||| Find the name of a free variable by its index
freeVarName : Fin vs -> FreeVars vs -> Name
freeVarName FZ     (x :< y) = fst y
freeVarName (FS x) (y :< z) = freeVarName x y

||| List of bound variable names in expression
||| @ bjn upper bound on bound variable de Bruijn index
namespace BoundVars
  public export
  data BoundVars : (bjn : Nat) -> Type where
    Lin  : BoundVars 0
    (:<) : BoundVars vs -> Name -> BoundVars (S vs)

||| Find the index of a free variable by its name
queryBV : Name -> BoundVars bjn -> Maybe $ Fin bjn
queryBV nm [<] = Nothing
queryBV nm (xs :< nm') = 
  if nm == nm' 
     then Just 0 
     else shift 1 <$> queryBV nm xs

||| Find the name of a bound variable by its index
boundVarName : Fin bjn -> BoundVars bjn -> Name
boundVarName FZ (x :< y) = y
boundVarName (FS x) (y :< z) = boundVarName x y

data ConversionError = UnsupportedExprError TTImp | NoNameError FC

assertName : MonadError ConversionError m => FC -> Maybe Name -> m Name
assertName fc Nothing  = throwError $ NoNameError fc
assertName fc (Just n) = pure n

convertToIR : MonadError ConversionError m => 
              FreeVars vs -> BoundVars bjn -> TTImp -> m $ IRTerm vs bjn
convertToIR freeVars boundVars (IVar fc nm) = 
  pure $ 
    fromMaybe (IRGlobalVar nm) $ 
      IRLocalVar <$> queryBV nm boundVars <|> 
      IRFreeVar  <$> queryFV nm freeVars
convertToIR freeVars boundVars (IPi fc rig pinfo mnm argTy retTy) = 
  pure $ IRPi rig 
              !(traverse (convertToIR freeVars boundVars) pinfo) 
              !(assertName fc mnm) 
              !(convertToIR freeVars boundVars argTy) 
              !(convertToIR freeVars (boundVars :< !(assertName fc mnm)) retTy)
convertToIR freeVars boundVars (ILam fc rig pinfo mnm argTy lamTy) = 
  pure $ IRLam rig 
               !(traverse (convertToIR freeVars boundVars) pinfo) 
               !(assertName fc mnm) 
               !(convertToIR freeVars boundVars argTy) 
               !(convertToIR freeVars (boundVars :< !(assertName fc mnm)) lamTy)
convertToIR freeVars boundVars (ILet fc lhsFC rig nm nTy nVal scope) = 
  pure $ IRLet rig nm 
               !(convertToIR freeVars boundVars nTy) 
               !(convertToIR freeVars boundVars nVal)
               !(convertToIR freeVars (boundVars :< nm) scope)
convertToIR freeVars boundVars (IApp fc s t) = 
  pure $ IRApp !(convertToIR freeVars boundVars s) 
               !(convertToIR freeVars boundVars t)
convertToIR freeVars boundVars (INamedApp fc s nm t) = 
  pure $ IRNamedApp !(convertToIR freeVars boundVars s) nm
                    !(convertToIR freeVars boundVars t)
convertToIR freeVars boundVars (IAutoApp fc s t) = 
  pure $ IRAutoApp !(convertToIR freeVars boundVars s) 
                   !(convertToIR freeVars boundVars t)
convertToIR freeVars boundVars (IPrimVal fc c) = pure $ IRPrim c
convertToIR freeVars boundVars (IType fc) = pure $ IRType
convertToIR freeVars boundVars term = throwError $ UnsupportedExprError term

convertFromIR : FreeVars vs -> BoundVars bjn -> IRTerm vs bjn -> TTImp
convertFromIR freeVars boundVars (IRFreeVar x) = 
  IVar EmptyFC $ freeVarName x freeVars
convertFromIR freeVars boundVars (IRLocalVar x) = 
  IVar EmptyFC $ boundVarName x boundVars
convertFromIR freeVars boundVars (IRGlobalVar nm) = 
  IVar EmptyFC nm
convertFromIR freeVars boundVars IRType = IType EmptyFC
convertFromIR freeVars boundVars (IRApp x y) = 
  IApp EmptyFC (convertFromIR freeVars boundVars x) 
               (convertFromIR freeVars boundVars y)
convertFromIR freeVars boundVars (IRAutoApp x y) = 
  IAutoApp EmptyFC (convertFromIR freeVars boundVars x) 
                   (convertFromIR freeVars boundVars y)
convertFromIR freeVars boundVars (IRNamedApp x nm y) = 
  INamedApp EmptyFC (convertFromIR freeVars boundVars x) nm 
                    (convertFromIR freeVars boundVars y)
convertFromIR freeVars boundVars (IRLam rig pinfo nm x y) = 
  ILam EmptyFC rig (convertFromIR freeVars boundVars <$> pinfo) (Just nm) 
                   (convertFromIR freeVars boundVars x) 
                   (convertFromIR freeVars (boundVars :< nm) y)
convertFromIR freeVars boundVars (IRPi rig pinfo nm x y) = 
  IPi EmptyFC rig (convertFromIR freeVars boundVars <$> pinfo) (Just nm) 
                  (convertFromIR freeVars boundVars x) 
                  (convertFromIR freeVars (boundVars :< nm) y)
convertFromIR freeVars boundVars (IRLet rig nm x y z) = 
  ILet EmptyFC EmptyFC rig nm (convertFromIR freeVars boundVars x) 
                              (convertFromIR freeVars boundVars y) 
                              (convertFromIR freeVars (boundVars :< nm) z)
convertFromIR freeVars boundVars (IRPrim c) = IPrimVal EmptyFC c

typeof : FreeVars vs -> IRTerm vs bjn -> IRTerm vs bjn
typeof freeVars (IRFreeVar x) = ?tof_rhs_0
typeof freeVars (IRLocalVar x) = ?tof_rhs_1
typeof freeVars (IRGlobalVar nm) = ?tof_rhs_2
typeof freeVars IRType = IRType
typeof freeVars (IRApp x y) = ?tof_rhs_4
typeof freeVars (IRAutoApp x y) = ?tof_rhs_5
typeof freeVars (IRNamedApp x nm y) = ?tof_rhs_6
typeof freeVars (IRLam rig pinfo nm x y) = IRPi rig pinfo nm x $ typeof freeVars y
typeof freeVars (IRPi rig pinfo nm x y) = IRType
typeof freeVars (IRLet rig nm x y z) = ?tof_rhs_9
typeof freeVars (IRPrim (I i)) = ?tof_rhs_11
typeof freeVars (IRPrim (BI i)) = ?tof_rhs_12
typeof freeVars (IRPrim (I8 i)) = ?tof_rhs_13
typeof freeVars (IRPrim (I16 i)) = ?tof_rhs_14
typeof freeVars (IRPrim (I32 i)) = ?tof_rhs_15
typeof freeVars (IRPrim (I64 i)) = ?tof_rhs_16
typeof freeVars (IRPrim (B8 m)) = ?tof_rhs_17
typeof freeVars (IRPrim (B16 m)) = ?tof_rhs_18
typeof freeVars (IRPrim (B32 m)) = ?tof_rhs_19
typeof freeVars (IRPrim (B64 m)) = ?tof_rhs_20
typeof freeVars (IRPrim (Str str)) = ?tof_rhs_21
typeof freeVars (IRPrim (Ch c)) = ?tof_rhs_22
typeof freeVars (IRPrim (Db dbl)) = ?tof_rhs_23
typeof freeVars (IRPrim (PrT pty)) = ?tof_rhs_24
typeof freeVars (IRPrim WorldVal) = IRType

data ReductionError = AppReductionError

-- TODO: Typechecking!
appReduce : MonadError ReductionError m => 
            (lhs : IRTerm vs bjn) -> (rhs: IRTerm vs bjn) -> m (IRTerm vs bjn)
appReduce (IRLam _ ExplicitArg _ ty body) rhs = pure $ subst' rhs 0 body
appReduce (IRLam rig pinfo nm ty body) rhs = IRLam rig pinfo nm ty <$> appReduce body (raise' 1 rhs)
appReduce (IRApp _ _) rhs = throwError AppReductionError
appReduce IRType rhs = throwError AppReductionError
appReduce (IRPi _ _ _ _ _) rhs = throwError AppReductionError
appReduce (IRPrim _) rhs = throwError AppReductionError
appReduce lhs rhs = pure lhs

autoAppReduce : MonadError ReductionError m => 
                (lhs : IRTerm vs bjn) -> (rhs : IRTerm vs bjn) -> m (IRTerm vs bjn)
autoAppReduce (IRLam _ AutoImplicit _ ty body) rhs = pure $ subst' rhs 0 body
autoAppReduce (IRLam rig pinfo nm ty body) rhs = IRLam rig pinfo nm ty <$> autoAppReduce body (raise' 1 rhs)
autoAppReduce IRType rhs = throwError AppReductionError
autoAppReduce (IRPi _ _ _ _ _) rhs = throwError AppReductionError
autoAppReduce (IRPrim _) rhs = throwError AppReductionError
autoAppReduce lhs rhs = pure lhs

namedAppReduce : MonadError ReductionError m => 
                 (lhs : IRTerm vs bjn) -> Name -> (rhs : IRTerm vs bjn) -> m (IRTerm vs bjn)
namedAppReduce (IRLam rig pinfo nm ty body) nm' rhs = if nm == nm' then pure $ subst' rhs 0 body else IRLam rig pinfo nm ty <$> namedAppReduce body nm' (raise' 1 rhs)
namedAppReduce IRType nm rhs = throwError AppReductionError
namedAppReduce (IRPi _ _ _ _ _) nm rhs = throwError AppReductionError
namedAppReduce (IRPrim _) nm rhs = throwError AppReductionError
namedAppReduce lhs nm rhs = pure lhs

reduce : MonadError ReductionError m => IRTerm vs bjn -> m $ IRTerm vs bjn
reduce (IRFreeVar id) = pure $ IRFreeVar id
reduce (IRLocalVar id) = pure $ IRLocalVar id
reduce (IRGlobalVar gn) = pure $ IRGlobalVar gn
reduce IRType = pure $ IRType
reduce (IRApp l r) = appReduce !(reduce l) !(reduce r)
reduce (IRAutoApp l r) = autoAppReduce !(reduce l) !(reduce r)
reduce (IRNamedApp l nm r) = namedAppReduce !(reduce l) nm !(reduce r)
reduce (IRLam rig pinfo nm ty body) = do
  pure $ IRLam rig !(traverse reduce pinfo) nm !(reduce ty) !(reduce body)
reduce (IRPi rig pinfo nm ty body) = pure $ IRPi rig !(traverse reduce pinfo) nm !(reduce ty) !(reduce body)
reduce (IRLet rig nm nTy nVal inner) = pure $ subst' nVal 0 inner
reduce (IRPrim c) = pure $ IRPrim c

data IRAppType = IRExplicit | IRAutoImplicit | IRNamed Name

record IRAppArg (vs : Nat) (bjn : Nat) where
  constructor MkAA
  argTy : IRAppType
  arg : IRTerm vs bjn

appArg : IRTerm vs bjn -> IRAppArg vs bjn -> IRTerm vs bjn
appArg l (MkAA IRExplicit arg) = IRApp l arg
appArg l (MkAA IRAutoImplicit arg) = IRAutoApp l arg
appArg l (MkAA (IRNamed nm) arg) = IRNamedApp l nm arg

peelAppTelescope : IRTerm vs bjn -> (IRTerm vs bjn, List $ IRAppArg vs bjn)
peelAppTelescope t = go t []
  where
  go : IRTerm vs bjn -> List (IRAppArg vs bjn) -> (IRTerm vs bjn, List $ IRAppArg vs bjn)
  go (IRApp l r) rest = go l $ MkAA IRExplicit r :: rest
  go (IRAutoApp l r) rest = go l $ MkAA IRAutoImplicit r :: rest
  go (IRNamedApp l nm r) rest = go l $ MkAA (IRNamed nm) r :: rest
  go t rest = (t, rest)

applyAppTelescope : IRTerm vs bjn -> List (IRAppArg vs bjn) -> IRTerm vs bjn
applyAppTelescope = foldl appArg

data UnificationError = UConversionError ConversionError | UReductionError ReductionError
