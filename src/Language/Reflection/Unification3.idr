module Language.Reflection.Unification3

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.Solver

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp
import Language.Reflection.Syntax

import Data.Fin
import Data.Nat
import Data.Vect
import Data.SortedMap

%default total

||| A bundle of non-global context and a term
%inline
Bundle : Nat -> Nat -> Type
Bundle fvs bjn = (FreeVars fvs, BoundVars fvs bjn, IRTerm fvs bjn)

%inline
HelpLR : (Nat -> t) -> (isLeft : Bool) -> (fvsL : Nat) -> (fvsR : Nat) -> t
HelpLR f isLeft fvsL fvsR =
  if isLeft then f fvsL else f fvsR

%inline
IRTerm' : Bool -> Nat -> Nat -> Nat -> Type
IRTerm' True  fvsL fvsR = IRTerm fvsL
IRTerm' False fvsL fvsR = IRTerm fvsR

%inline
Bundle' : Bool -> Nat -> Nat -> Nat -> Type
Bundle' True  fvsL fvsR = Bundle fvsL
Bundle' False fvsL fvsR = Bundle fvsR

%inline
Constraints' : Bool -> Nat -> Nat ->Type
Constraints' True fvs fvs' = Constraints fvs fvs'
Constraints' False fvs fvs' = Constraints fvs' fvs

record AppChain (fvs : Nat) (bjn : Nat)

mkAC : IRTerm fvs bjn -> AppChain fvs bjn

%inline
AppBundle' : Bool -> Nat -> Nat -> Nat -> Type
AppBundle' True fvsL fvsR bjn = (FreeVars fvsL, BoundVars fvsL bjn, AppChain fvsL bjn)
AppBundle' False fvsL fvsR bjn = (FreeVars fvsR, BoundVars fvsR bjn, AppChain fvsR bjn)

%inline
AppBundle : Nat -> Nat -> Type
AppBundle fvs bjn = (FreeVars fvs, BoundVars fvs bjn, AppChain fvs bjn)

{b : Bool} -> Monad m => (ms1 : MonadState s1 m) => (ms2: MonadState s2 m) => MonadState (if b then s1 else s2) m where
  get {b = True} = get @{ms1}
  get {b = False} = get @{ms2}
  put {b = True} = put @{ms1}
  put {b = False} = put @{ms2}
  state {b = True} = state @{ms1}
  state {b = False} = state @{ms2}


||| Tries to reduce a bundle
|||
||| Errors if functions are applied with incorrect arguments (TODO explain further)
||| or if typechecking fails
public export
reduce : Monad m =>
         MonadError UnificationError m => 
         MonadState (Constraints fvsL fvsR) m =>
         GlobalVars ->
         (isLeft : Bool) ->
         Bundle' isLeft fvsL fvsR bjn ->
         m $ IRTerm' isLeft fvsL fvsR bjn

||| Given the context of free and bound variables, determine the type of an expression
||| If contains type of expression 
public export
typeof : Monad m =>
         MonadError UnificationError m => 
         MonadState (Constraints fvsL fvsR) m =>
         {bjn : Nat} -> 
         GlobalVars -> 
         (isLeft : Bool) ->
         Bundle' isLeft fvsL fvsR bjn ->
         m $ IRTerm' isLeft fvsL fvsR bjn

||| Register that the two expressions must be equal
public export
unify : Monad m =>
        MonadError UnificationError m =>
        MonadState (Constraints fvsL fvsR) m =>
        GlobalVars ->
        (isLeft : Bool) -> 
        Bundle' isLeft fvsL fvsR bjn ->
        (isLeft' : Bool) ->
        Bundle' isLeft' fvsL fvsR bjn' ->
        m $ ()

public export
typeofAppChain : Monad m =>
                 MonadError UnificationError m =>
                 MonadState (Constraints fvsL fvsR) m => 
                 GlobalVars ->
                 {bjn : Nat} ->
                 (isLeft : Bool) ->
                 AppBundle' isLeft fvsL fvsR bjn ->
                 m $ IRTerm' isLeft fvsL fvsR bjn

typeofAppChain' : 
  Monad m =>
  MonadError UnificationError m =>
  {bjn : Nat} ->
  (isLeft : Bool) ->
  MonadState (Constraints' isLeft fvs fvs') m =>
  GlobalVars ->
  AppBundle fvs bjn ->
  m $ IRTerm fvs bjn

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

typeof' : Monad m =>
          MonadError UnificationError m =>
          {bjn : Nat} ->
          (isLeft : Bool) ->
          MonadState (Constraints' isLeft fvs fvs') m =>
          GlobalVars ->
          Bundle fvs bjn ->
          m $ IRTerm fvs bjn
typeof' isLeft gv (fv, bv, (IRFreeVar x)) = 
  pure $ raise bjn $ snd $ index x fv
typeof' isLeft gv (fv, bv, (IRLocalVar x)) = 
  pure $ snd $ index x bv
typeof' isLeft gv (fv, bv, (IRGlobalVar nm)) =
  case lookup nm gv of
    Just (t, _) => pure $ setFV $ raise bjn t
    Nothing => throwError $ GlobalVarNotFound nm
typeof' isLeft gv (fv, bv, IRType) = pure IRType
typeof' isLeft gv (fv, bv, a@(IRApp x y)) = 
  assert_total $ typeofAppChain' {fvs'} isLeft gv (fv, bv, mkAC a)
typeof' isLeft gv (fv, bv, a@(IRAutoApp x y)) = 
  assert_total $ typeofAppChain' {fvs'} isLeft gv (fv, bv, mkAC a)
typeof' isLeft gv (fv, bv, a@(IRNamedApp x nm y)) = 
  assert_total $ typeofAppChain' {fvs'} isLeft gv (fv, bv, mkAC a)
typeof' isLeft gv (fv, bv, (IRPi rig pinfo nm x y)) = pure IRType
typeof' isLeft gv (fv, bv, (IRPrim c)) = pure $ typeofConst c
typeof' isLeft gv (fv, bv, (IRLam rig pinfo nm x y)) with 
  (IRPi rig pinfo nm x <$>
    assert_total (typeof' {m} {fvs'} isLeft gv (fv, bv :< (nm, x), y)))
  typeof' True _ (_, _, (IRLam _ _ _ _ _)) | res = res
  typeof' False _ (_, _, (IRLam _ _ _ _ _)) | res = res

typeof' isLeft gv (fv, bv, (IRLet rig nm type val body)) with 
  (do
    valT <- typeof' {m} {fvs'} isLeft gv (fv, bv, val)
    if isLeft
       then unify gv True (fv, bv, valT) True (fv, bv, type)
       else unify gv False (fv, bv, valT) False (fv, bv, type)
    assert_total (typeof' {m} {fvs'} isLeft gv (fv, bv, subst' val 0 body)))
  typeof' True _ (_, _, IRLet _ _ _ _ _) | res = res
  typeof' False _ (_, _, IRLet _ _ _ _ _) | res = res

typeof gv False b = typeof' {m} False gv b
typeof gv True b = typeof' {m} True gv b

reduce' : Monad m =>
          MonadError UnificationError m =>
          (isLeft : Bool) ->
          MonadState (Constraints' isLeft fvs fvs') m =>
          GlobalVars ->
          Bundle fvs bjn ->
          m $ IRTerm fvs bjn
reduce' isLeft gv (fv, bv, (IRFreeVar x)) = pure $ IRFreeVar x
reduce' isLeft gv (fv, bv, (IRLocalVar x)) = pure $ IRLocalVar x
reduce' isLeft gv (fv, bv, (IRGlobalVar nm)) = pure $ IRGlobalVar nm
reduce' isLeft gv (fv, bv, IRType) = pure $ IRType
reduce' isLeft gv (fv, bv, (IRApp x y)) = ?red_rhs_0
reduce' isLeft gv (fv, bv, (IRAutoApp x y)) = ?red_rhs_1
reduce' isLeft gv (fv, bv, (IRNamedApp x nm y)) = ?red_rhs_2
reduce' isLeft gv (fv, bv, (IRPrim c)) = pure $ IRPrim c
reduce' isLeft gv (fv, bv, (IRLet rig nm type val body)) = 
  pure $ subst' val 0 body
reduce' isLeft gv (fv, bv, (IRLam rig pinfo nm x y)) with (
  IRLam rig 
    <$> traverse (\n => assert_total (reduce' {fvs'} isLeft gv (fv, bv, n))) pinfo
    <*> pure nm
    <*> reduce' {m} {fvs'} isLeft gv (fv, bv, x)
    <*> assert_total (reduce' {fvs'} isLeft gv (fv, bv :< (nm, x), y)))
  reduce' True gv (fv, bv, (IRLam rig pinfo nm x y)) | res = res
  reduce' False gv (fv, bv, (IRLam rig pinfo nm x y)) | res = res
reduce' isLeft gv (fv, bv, (IRPi rig pinfo nm x y)) with (
  IRPi rig 
    <$> traverse (\n => assert_total (reduce' {fvs'} isLeft gv (fv, bv, n))) pinfo
    <*> pure nm
    <*> reduce' {m} {fvs'} isLeft gv (fv, bv, x)
    <*> assert_total (reduce' {fvs'} isLeft gv (fv, bv :< (nm, x), y)))
  reduce' True gv (fv, bv, (IRPi rig pinfo nm x y)) | res = res
  reduce' False gv (fv, bv, (IRPi rig pinfo nm x y)) | res = res

reduce gv False b = reduce' {m} False gv b
reduce gv True b = reduce' {m} True gv b

data IRAppType = IRExplicit | IRAutoImplicit | IRNamed Name

record IRAppArg (fvs : Nat) (bjn : Nat) where
  constructor MkAA
  argTy : IRAppType
  arg : IRTerm fvs bjn


appArg : IRTerm fvs bjn -> IRAppArg fvs bjn -> IRTerm fvs bjn
appArg l (MkAA IRExplicit arg) = IRApp l arg
appArg l (MkAA IRAutoImplicit arg) = IRAutoApp l arg
appArg l (MkAA (IRNamed nm) arg) = IRNamedApp l nm arg

peelAppTelescope : IRTerm fvs bjn -> (IRTerm fvs bjn, List $ IRAppArg fvs bjn)
peelAppTelescope t = go t []
  where
  go : IRTerm fvs bjn -> 
       List (IRAppArg fvs bjn) -> 
       (IRTerm fvs bjn, List $ IRAppArg fvs bjn)
  go (IRApp l r) rest = go l $ MkAA IRExplicit r :: rest
  go (IRAutoApp l r) rest = go l $ MkAA IRAutoImplicit r :: rest
  go (IRNamedApp l nm r) rest = go l $ MkAA (IRNamed nm) r :: rest
  go t rest = (t, rest)

applyAppTelescope : IRTerm fvs bjn -> List (IRAppArg fvs bjn) -> IRTerm fvs bjn
applyAppTelescope = foldl appArg

record AppChain' (fvs : Nat) (bjn : Nat) where
  constructor MkAppChain'
  lhs : IRTerm fvs bjn
  explicits : SnocList (IRTerm fvs bjn)
  autos : SnocList (IRTerm fvs bjn)
  nameds : SortedMap Name $ IRTerm fvs bjn

addAppArg : IRAppArg fvs bjn -> AppChain' fvs bjn -> AppChain' fvs bjn
addAppArg (MkAA IRExplicit arg) = {explicits $= (:< arg)}
addAppArg (MkAA IRAutoImplicit arg) = {autos $= (:< arg)}
addAppArg (MkAA (IRNamed nm) arg) = {nameds $= insert nm arg}

record AppChain (fvs : Nat) (bjn : Nat) where
  constructor MkAppChain
  lhs : IRTerm fvs bjn
  explicits : List (IRTerm fvs bjn)
  autos : List (IRTerm fvs bjn)
  nameds : SortedMap Name $ IRTerm fvs bjn

toAC : AppChain' fvs bjn -> AppChain fvs bjn
toAC (MkAppChain' lhs explicits autos nameds) = 
  MkAppChain lhs (toList explicits) (toList autos) nameds

mkAC t = do
  let (lhs, args) = peelAppTelescope t
  let ac' = foldl (flip addAppArg) (MkAppChain' lhs [<] [<] empty) args
  toAC ac'

acEmpty : AppChain fv bjn -> Bool
acEmpty (MkAppChain lhs [] [] nameds) = nameds == empty
acEmpty (MkAppChain lhs _ _ nameds) = False

typecheck :
  Monad m =>
  MonadError UnificationError m =>
  {bjn : Nat} ->
  (isLeft : Bool) ->
  MonadState (Constraints' isLeft fvs fvs') m =>
  GlobalVars ->
  (var : Bundle fvs bjn) ->
  (ty : IRTerm fvs bjn) ->
  m ()
typecheck False gv b@(fv, bv, val) ty = do
  ty <- typeof' {m} False gv b
  unify gv False b False (fv, bv, ty)
typecheck True gv b@(fv, bv, val) ty = do
  ty <- typeof' {m} True gv b
  unify gv True b True (fv, bv, ty)

acSigNext : 
  Monad m =>
  MonadError UnificationError m =>
  GlobalVars ->
  IRTerm fvs bjn ->
  AppBundle fvs bjn ->
  m $ (IRTerm fvs bjn, IRTerm fvs bjn, IRTerm fvs (S bjn), AppChain fvs bjn)
acSigNext gv lhsSig (fv, bv, ac) = 
  case lhsSig of
    (IRPi rig ImplicitArg nm x y) =>
      case lookup nm ac.nameds of
         Nothing => throwError AppNameNotFoundError
         Just av => pure (av, x, y, {nameds $= delete nm} ac)
    (IRPi rig ExplicitArg nm x y) =>
      case ac.explicits of
        [] => case lookup nm ac.nameds of
          Nothing => throwError AppNameNotFoundError
          Just av => pure (av, x, y, {nameds $= delete nm} ac)
        (av :: xs) => pure (av, x, y, {explicits := xs} ac)
    (IRPi rig AutoImplicit nm x y) => 
      case ac.autos of
        [] => case lookup nm ac.nameds of
          Nothing => throwError AppNameNotFoundError
          Just av => pure (av, x, y, {nameds $= delete nm} ac)
        (av :: xs) => pure (av, x, y, {autos := xs} ac)
    (IRPi rig (DefImplicit z) nm x y) =>
       case lookup nm ac.nameds of
           Nothing => pure (z, x, y, ac)
           Just av => pure (av, x, y, {nameds $= delete nm} ac)
    _ => throwError AppBadLhsError

acSigReduce : 
  Monad m =>
  MonadError UnificationError m =>
  {bjn : Nat} ->
  (isLeft : Bool) ->
  MonadState (Constraints' isLeft fvs fvs') m =>
  GlobalVars ->
  IRTerm fvs bjn ->
  AppBundle fvs bjn ->
  m $ IRTerm fvs bjn
acSigReduce isLeft gv lhsSig (fv, bv, ac) = 
  if acEmpty ac then pure lhsSig else do
    (argVal, argTy, body, nextAC) <- acSigNext gv lhsSig (fv, bv, ac)
    typecheck {fvs'} isLeft gv (fv, bv, argVal) argTy
    assert_total $ acSigReduce {m} {fvs'} isLeft gv (subst' argVal 0 body) (fv, bv, nextAC)
  

typeofAppChain' isLeft gv (fv, bv, chain) = do
  sig <- typeof' {m} {fvs'} isLeft gv (fv, bv, chain.lhs)
  acSigReduce {m} {fvs'} isLeft gv sig (fv, bv, chain)

typeofAppChain gv False b = typeofAppChain' False gv b
typeofAppChain gv True b = typeofAppChain' True gv b
