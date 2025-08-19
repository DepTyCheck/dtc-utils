module Language.Reflection.Unification3.Convert

import Data.Maybe
import Data.Fin

import Control.Monad.Error.Interface

import Language.Reflection.Unification3.IR
import Language.Reflection.Unification3.Context.Main
import Language.Reflection.Unification3.Error

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp

||| Throw an error st FC if Nothing, otherwise return name
assertName : MonadError UnificationError m => FC -> Maybe Name -> m Name
assertName fc Nothing  = throwError $ NoNameError fc
assertName fc (Just n) = pure n

public export
convertToIR : MonadError UnificationError m => 
              FreeVars fvs -> BoundNames bjn -> TTImp -> m $ IRTerm fvs bjn
convertToIR freeVars boundVars (IVar fc nm) = 
  pure $ 
    fromMaybe (IRGlobalVar nm) $ 
      IRLocalVar <$> queryBN nm boundVars <|> 
      IRFreeVar  <$> queryFV nm freeVars
convertToIR freeVars boundVars (IPi fc rig pinfo mnm argTy retTy) = 
  IRPi rig <$> traverse (convertToIR freeVars boundVars) pinfo
           <*> assertName fc mnm
           <*> convertToIR freeVars boundVars argTy
           <*> convertToIR freeVars (boundVars :< !(assertName fc mnm)) retTy
convertToIR freeVars boundVars (ILam fc rig pinfo mnm argTy lamTy) = 
  IRLam rig <$> traverse (convertToIR freeVars boundVars) pinfo
            <*> assertName fc mnm
            <*> convertToIR freeVars boundVars argTy
            <*> convertToIR freeVars (boundVars :< !(assertName fc mnm)) lamTy
convertToIR freeVars boundVars (ILet fc lhsFC rig nm nTy nVal scope) = 
  IRLet rig nm <$> convertToIR freeVars boundVars nTy
               <*> convertToIR freeVars boundVars nVal
               <*> convertToIR freeVars (boundVars :< nm) scope
convertToIR freeVars boundVars (IApp fc s t) = 
  IRApp <$> convertToIR freeVars boundVars s
               <*> convertToIR freeVars boundVars t
convertToIR freeVars boundVars (INamedApp fc s nm t) = 
  IRNamedApp <$> convertToIR freeVars boundVars s
             <*> pure nm
             <*> convertToIR freeVars boundVars t
convertToIR freeVars boundVars (IAutoApp fc s t) = 
  IRAutoApp <$> convertToIR freeVars boundVars s 
            <*> convertToIR freeVars boundVars t
convertToIR freeVars boundVars (IPrimVal fc c) = pure $ IRPrim c
convertToIR freeVars boundVars (IType fc) = pure $ IRType
convertToIR freeVars boundVars term = throwError $ UnsupportedExprTypeError $ getFC term

public export
convertFreeVars : MonadError UnificationError m => 
                  (l : SnocList (Name, TTImp)) -> m $ FreeVars (length l)
convertFreeVars [<] = pure [<]
convertFreeVars (sx :< (n, t)) = do
  ffvs' <- convertFreeVars sx
  x' <- convertToIR ffvs' [<] t
  pure $ ffvs' :< (n, x')

public export
convertFromIR : FreeVars fvs -> BoundNames bjn -> IRTerm fvs bjn -> TTImp
convertFromIR freeVars boundVars (IRFreeVar x) = 
  IVar EmptyFC $ freeVarName x freeVars
convertFromIR freeVars boundVars (IRLocalVar x) = 
  IVar EmptyFC $ boundName x boundVars
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

