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
GlobalVars : Type
GlobalVars = SortedMap Name (IRTerm 0 0, NameType)

populateGVIR : Monad m =>
               Elaboration m =>
               MonadState GlobalVars m =>
               MonadError UnificationError m =>
               IRTerm fvs bjn ->
               m (IRTerm fvs bjn)
populateGVIR = mapMIR $ \case 
  t@(IRGlobalVar nm) => do
    Nothing <- gets $ lookup nm
      | Just _ => pure t
    ((n, ty) :: []) <- getType nm
      | [] => throwError $ GlobalVarNotFound nm
      | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
    ((n', i) :: []) <- getInfo nm
      | [] => throwError $ GlobalVarNotFound nm
      | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
    converted <- convertToIR [<] [<] ty
    modify $ insert nm (converted, i.nametype)
    pure t
  t => pure t

populateGV : Monad m =>
             Elaboration m =>
             MonadError UnificationError m =>
             IRTerm fvs bjn ->
             GlobalVars ->
             m GlobalVars
populateGV term gv = execStateT gv $ populateGVIR term

