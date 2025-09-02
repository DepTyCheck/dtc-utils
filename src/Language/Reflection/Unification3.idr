module Language.Reflection.Unification3

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.IR.AppChain
import public Language.Reflection.Unification3.Solver
import public Language.Reflection.Unification3.Log

import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.State

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax

import public Data.Fin
import public Data.Nat
import public Data.Vect
import public Data.SortedMap

public export
record Bounds where
  constructor MKBounds
  fvsL : Nat
  fvsR : Nat

public export
%inline
{b : Bool} -> 
{bds : Bounds} ->
Monad m => 
(ms1 : MonadState (Constraints bds.fvsL bds.fvsR) m) => 
(ms2 : MonadState (Constraints bds.fvsR bds.fvsL) m) => 
MonadState (Constraints (if b then bds.fvsL else bds.fvsR) (if b then bds.fvsR else bds.fvsL)) m where
  get {b = True} = get @{ms1}
  get {b = False} = get @{ms2}
  put {b = True} = put @{ms1}
  put {b = False} = put @{ms2}
  state {b = True} = state @{ms1}
  state {b = False} = state @{ms2}

parameters 
  (isTrue : Bool)
  (b : Bounds)

  %inline
  public export
  thisFvs : Nat
  thisFvs = if isTrue then b.fvsL else b.fvsR

  %inline
  public export
  otherFvs : Nat
  otherFvs = if isTrue then b.fvsR else b.fvsL

  %inline
  public export
  term : Nat -> Type
  term = IRTerm thisFvs

  %inline
  public export
  fvsT : Type
  fvsT = FreeVars thisFvs

  %inline
  public export
  bvsT : Nat -> Type
  bvsT = BoundVars thisFvs

  %inline
  public export
  constraints : Type
  constraints = Constraints b.fvsL b.fvsR

  %inline
  public export
  appChain : Nat -> Type
  appChain = AppChain thisFvs

public export
typeofConst : Constant -> IRTerm fvs bjn
typeofConst (I i) = IRGlobalVar "Int"
typeofConst (BI i) = IRGlobalVar "Integer"
typeofConst (I8 i) = IRGlobalVar "Int8"
typeofConst (I16 i) = IRGlobalVar "Int16"
typeofConst (I32 i) = IRGlobalVar "Int32"
typeofConst (I64 i) = IRGlobalVar "Int64"
typeofConst (B8 m) = IRGlobalVar "Bits8"
typeofConst (B16 m) = IRGlobalVar "Bits16"
typeofConst (B32 m) = IRGlobalVar "Bits32"
typeofConst (B64 m) = IRGlobalVar "Bits64"
typeofConst (Str str) = IRGlobalVar "String"
typeofConst (Ch c) = IRGlobalVar "Char"
typeofConst (Db dbl) = IRGlobalVar "Double"
typeofConst (PrT pty) = IRGlobalVar "PrimType"
typeofConst WorldVal = IRType

parameters 
  {auto _ : Monad m}
  {auto _ : MonadError UnificationError m}
  {auto _ : MonadLog m}
  (gv : GlobalVars)
  {bds : Bounds}

  public export
  unify : MonadState (Constraints bds.fvsL bds.fvsR) m =>
          (isLeft : Bool) ->
          (fv : fvsT isLeft bds) ->
          (bv : bvsT isLeft bds bjn) ->
          (t : term isLeft bds bjn) ->
          (isLeft' : Bool) ->
          (fv' : fvsT isLeft' bds) ->
          (bv : bvsT isLeft' bds bjn) ->
          (t' : term isLeft' bds bjn) ->
          m ()

  parameters 
    (isLeft : Bool)
    {auto st : MonadState (constraints isLeft bds) m}
    (fv : fvsT isLeft bds)
    parameters
      {bjn : Nat}
      (bv : bvsT isLeft bds bjn)

      public export
      typeof : term isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      typeofAppChain : appChain isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      reduce : term isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      reduceAppChain : appChain isLeft bds bjn -> m $ term isLeft bds bjn 

      public export
      typecheck : term isLeft bds bjn -> term isLeft bds bjn -> m ()
      typecheck val type = do
        valT <- typeof val
        unify isLeft fv bv valT isLeft fv bv type
    
    typeof bv t = do
      logStr 10 "typeof \{show isLeft} \{show t}"
      case t of
        IRFreeVar x => pure $ raise bjn $ snd $ index x fv
        IRLocalVar x => pure $ snd $ index x bv
        IRGlobalVar nm =>
          case lookup nm gv of
            Just (t, _) => pure $ setFV $ raise bjn t
            Nothing => throwError $ GlobalVarNotFound nm
        IRType => pure IRType
        t@(IRApp x y) => typeofAppChain isLeft fv bv $ mkAC t
        t@(IRAutoApp x y) => typeofAppChain isLeft fv bv $ mkAC t
        t@(IRNamedApp x nm y) => typeofAppChain isLeft fv bv $ mkAC t
        IRLam rig pinfo nm x y =>
          IRPi rig pinfo nm x <$> typeof isLeft fv (bv :< (nm, x)) y
        IRPi rig pinfo nm x y => pure IRType
        IRLet rig nm type val body => do
          valT <- typeof isLeft fv bv val
          unify isLeft fv bv valT isLeft fv bv type
          typeof isLeft fv bv $ subst' val 0 body
        IRPrim c => pure $ typeofConst c

    reduce bv t = do
      logStr 10 "reduce \{show isLeft} \{show t}"
      case t of
        IRFreeVar x => pure $ IRFreeVar x
        IRLocalVar x => pure $ IRLocalVar x
        IRGlobalVar nm => pure $ IRGlobalVar nm
        IRType => pure $ IRType
        t@(IRApp x y) => reduceAppChain isLeft fv bv $ mkAC t
        t@(IRAutoApp x y) => reduceAppChain isLeft fv bv $ mkAC t
        t@(IRNamedApp x nm y) => reduceAppChain isLeft fv bv $ mkAC t
        IRLam rig pinfo nm x y => do
          IRLam rig
            <$> traverse (\n => reduce isLeft fv bv n) pinfo
            <*> pure nm
            <*> reduce isLeft fv bv x
            <*> reduce isLeft fv (bv :< (nm, x)) y 
        IRPi rig pinfo nm x y => do
          IRPi rig
            <$> traverse (\n => reduce isLeft fv bv n) pinfo
            <*> pure nm
            <*> reduce isLeft fv bv x
            <*> reduce isLeft fv (bv :< (nm, x)) y 
        IRLet rig nm type val body => do
          typecheck isLeft fv bv val type
          reduce isLeft fv bv $ subst' val 0 body
        IRPrim c => pure $ IRPrim c

    typeofAppChain bv ac = do
      logStr 10 "typeofAppChain \{show isLeft} lhs=\{show ac.lhs} args=\{show $ ac.args} nameds = \{show $ ac.nameds}"
      -- lhs' <- reduce bv ac.lhs
      -- let ac = {lhs := lhs'} ac
      if ac.argCount == 0 
         then typeof isLeft fv bv ac.lhs 
         else case ac.lhs of
          IRLam rig pinfo nm ty body => do
            let Just (arg, ac) = nextArg pinfo nm ac
            | Nothing => throwError $ AppNameNotFoundError nm
            typecheck isLeft fv bv arg ty
            typeofAppChain isLeft fv bv $ 
              {lhs := subst' arg 0 body} ac
          IRGlobalVar _ => do
            typeof_lhs <- typeof bv ac.lhs
            pure $ unAC $ {lhs := typeof_lhs} ac
          _ => throwError AppBadLhsError

    reduceAppChain bv ac = do
      logStr 10 "reduceAppChain \{show isLeft} lhs=\{show ac.lhs} args=\{show $ ac.args}  nameds = \{show $ ac.nameds}"
      -- lhs' <- reduce bv ac.lhs
      -- let ac = {lhs := lhs'} ac
      if ac.argCount == 0
        then reduce isLeft fv bv ac.lhs
        else case ac.lhs of
          IRLam rig pinfo nm ty body => do
            let Just (arg, ac) = nextArg pinfo nm ac
            | Nothing => throwError $ AppNameNotFoundError nm
            typecheck isLeft fv bv arg ty
            reduceAppChain isLeft fv bv $ 
              {lhs := subst' arg 0 body} ac
          IRGlobalVar _ => pure $ unAC ac
          _ => throwError AppBadLhsError

  -- TODO: Impl unify
  unify isLeft fv bv t isLeft' fv' x t' = pure ()
