module Language.Reflection.Unification3.Context.GlobalVars

import Control.Monad.Error.Interface
import Control.Monad.State

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.Unification3.IR
import Language.Reflection.Unification3.Error
import Language.Reflection.Unification3.Context.Main
import Language.Reflection.Unification3.Convert

import Data.SortedMap

%default total

public export
GlobalVars : (fvs : Nat) -> Type
GlobalVars fvs = SortedMap Name (IRTerm fvs 0, NameType)

populateGVIR : Monad m =>
               Elaboration m =>
               MonadState (GlobalVars fvs) m =>
               MonadError UnificationError m =>
               FreeVars fvs ->
               IRTerm fvs bjn ->
               m (IRTerm fvs bjn)
populateGVIR fvs = mapMIR $ \case 
  t@(IRGlobalVar nm) => do
    Nothing <- gets $ lookup nm
      | Just _ => pure t
    ((n, ty) :: []) <- getType nm
      | [] => throwError $ GlobalVarNotFound nm
      | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
    ((n', i) :: []) <- getInfo nm
      | [] => throwError $ GlobalVarNotFound nm
      | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
    converted <- convertToIR fvs [<] ty
    modify $ insert nm (converted, i.nametype)
    pure t
  t => pure t

populateGV : Monad m =>
             Elaboration m =>
             MonadError UnificationError m =>
             FreeVars fvs ->
             IRTerm fvs bjn ->
             GlobalVars fvs ->
             m (GlobalVars fvs)
populateGV fv term gv = execStateT gv $ populateGVIR fv term

