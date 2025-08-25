module Language.Reflection.Unification3.Context.GlobalVars

import public Control.Monad.Either
import public Control.Monad.State

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.Context.Main
import public Language.Reflection.Unification3.Convert

import public Data.SortedMap
import public Data.SortedMap.Dependent

%default total

public export
GlobalVars : Type
GlobalVars = SortedMap Name (IRTerm 0 0, NameType)

public export
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

public export
populateGV : Monad m =>
             Elaboration m =>
             MonadError UnificationError m =>
             IRTerm fvs bjn ->
             GlobalVars ->
             m GlobalVars
populateGV term gv = execStateT gv $ populateGVIR term

public export
mockGV' : Monad m =>
         Elaboration m => 
         MonadError UnificationError m =>
         List Name ->
         GlobalVars ->
         m GlobalVars
mockGV' [] gv = pure gv
mockGV' (nm :: nms) gv = do
  let Nothing = lookup nm gv
    | Just _ => mockGV' nms gv
  ((n, ty) :: []) <- getType nm
    | [] => throwError $ GlobalVarNotFound nm
    | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
  ((n', i) :: []) <- getInfo nm
    | [] => throwError $ GlobalVarNotFound nm
    | mult => throwError $ AmbiguousGlobalVarError nm $ map fst mult
  converted <- convertToIR [<] [<] ty
  insert nm (converted, i.nametype) <$> mockGV' nms gv

public export
mockGV : List Name ->
         Elab GlobalVars
mockGV l = do
  Right answer <- 
    runEitherT {e=UnificationError} {m=Elab} $ mockGV' l empty
  | Left err => fail $ show err
  pure answer
