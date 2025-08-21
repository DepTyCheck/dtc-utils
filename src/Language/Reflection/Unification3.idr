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
Bundle : Nat -> Nat -> Type
Bundle fvs bjn = (FreeVars fvs, BoundVars fvs bjn, IRTerm fvs bjn)

HelpLR : (Nat -> t) -> (isLeft : Bool) -> (fvsL : Nat) -> (fvsR : Nat) -> t
HelpLR f isLeft fvsL fvsR =
  if isLeft then f fvsL else f fvsR

IRTerm' : Bool -> Nat -> Nat -> Nat -> Type
IRTerm' b fvsL fvsR = IRTerm (if b then fvsL else fvsR)

Bundle' : Bool -> Nat -> Nat -> Nat -> Type
Bundle' b fvsL fvsR = Bundle (if b then fvsL else fvsR)

Constraints' : Bool -> Nat -> Nat ->Type
Constraints' isLeft fvs fvs' = Constraints (if isLeft then fvs else fvs') (if isLeft then fvs' else fvs)


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
        Bundle' isLeft' fvsL fvsR bjn ->
        m $ ()

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
typeof' isLeft gv (fv, bv, (IRApp x y)) = ?typeof_rhs_4
typeof' isLeft gv (fv, bv, (IRAutoApp x y)) = ?typeof_rhs_5
typeof' isLeft gv (fv, bv, (IRNamedApp x nm y)) = ?typeof_rhs_6
typeof' isLeft gv (fv, bv, (IRPi rig pinfo nm x y)) = pure IRType
typeof' isLeft gv (fv, bv, (IRPrim c)) = pure $ typeofConst c
typeof' isLeft gv (fv, bv, (IRLam rig pinfo nm x y)) with (
  IRPi rig pinfo nm x <$>
  assert_total (typeof' {m} {fvs'} isLeft gv (fv, bv :< (nm, x), y)))
  typeof' True _ (_, _, (IRLam _ _ _ _ _)) | res = res
  typeof' False _ (_, _, (IRLam _ _ _ _ _)) | res = res

typeof' True gv (fv, bv, (IRLet rig nm type val body)) = do
  valT <- typeof' True gv (fv, bv, val)
  unify gv True (fv, bv, valT) True (fv, bv, type)
  assert_total typeof' True gv (fv, bv, subst' val 0 body)

typeof' False gv (fv, bv, (IRLet rig nm type val body)) = do
  valT <- typeof' False gv (fv, bv, val)
  unify gv False (fv, bv, valT) False (fv, bv, type)
  assert_total typeof' False gv (fv, bv, subst' val 0 body)

typeof gv False b = typeof' {m} False gv b
typeof gv True b = typeof' {m} True gv b

reduceL : Monad m =>
         MonadError UnificationError m => 
         MonadState (Constraints fvsL fvsR) m =>
         GlobalVars ->
         Bundle fvsL bjn  -> 
         m $ IRTerm fvsL bjn 
reduceL gv (fv, bv, (IRFreeVar x)) = pure $ IRFreeVar x
reduceL gv (fv, bv, (IRLocalVar x)) = pure $ IRLocalVar x
reduceL gv (fv, bv, (IRGlobalVar nm)) = pure $ IRGlobalVar nm
reduceL gv (fv, bv, IRType) = pure $ IRType
reduceL gv (fv, bv, (IRApp x y)) = ?rhrhrh_4
reduceL gv (fv, bv, (IRAutoApp x y)) = ?rhrhrh_5
reduceL gv (fv, bv, (IRNamedApp x nm y)) = ?rhrhrh_6
reduceL gv (fv, bv, (IRLam rig pinfo nm x y)) = 
  IRLam rig 
    <$> traverse (\n => assert_total reduceL gv (fv, bv, n)) pinfo
    <*> pure nm
    <*> reduceL gv (fv, bv, x)
    <*> assert_total reduceL gv (fv, bv :< (nm, x), y)
reduceL gv (fv, bv, (IRPi rig pinfo nm x y)) = 
 IRPi rig 
    <$> traverse (\n => assert_total reduceL gv (fv, bv, n)) pinfo
    <*> pure nm
    <*> reduceL gv (fv, bv, x)
    <*> assert_total reduceL gv (fv, bv :< (nm, x), y)
reduceL gv (fv, bv, (IRLet rig nm type val body)) = 
  pure $ subst' val 0 body
reduceL gv (fv, bv, (IRPrim c)) = pure $ IRPrim c

{b : Bool} -> Monad m => (ms1 : MonadState s1 m) => (ms2: MonadState s2 m) => MonadState (if b then s1 else s2) m where
  get {b = True} = get @{ms1}
  get {b = False} = get @{ms2}
  put {b = True} = put @{ms1}
  put {b = False} = put @{ms2}
  state {b = True} = state @{ms1}
  state {b = False} = state @{ms2}


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

mkAC : IRTerm fvs bjn -> AppChain fvs bjn
mkAC t = do
  let (lhs, args) = peelAppTelescope t
  let ac' = foldl (flip addAppArg) (MkAppChain' lhs [<] [<] empty) args
  toAC ac'
--
-- -- TODO: TYPECHECK THIS!
-- -- covering
-- sigReduce' : MonadError UnificationError m => 
--             IRTerm fvs bjn -> 
--             AppChain fvs bjn -> 
--             m $ IRTerm fvs bjn
-- sigReduce' (IRPi rig ImplicitArg nm x y) chain = 
--   case lookup nm chain.nameds of
--     Nothing => throwError ?tr_rhs_10
--     Just av => sigReduce' 
--                 (subst' av 0 y) 
--                 (assert_smaller chain $ {nameds $= delete nm} chain) 
-- sigReduce' (IRPi rig ExplicitArg nm x y) 
--           chain@(MkAppChain lhs [] autos nameds) = 
--   case lookup nm nameds of
--     Nothing => throwError ?tr_rhs_11
--     Just av => 
--       sigReduce'
--         (subst' av 0 y)
--         (assert_smaller nameds $ MkAppChain lhs [] autos $ delete nm nameds)
-- sigReduce' (IRPi rig ExplicitArg nm x y) 
--           (MkAppChain lhs (z :: xs) autos nameds) =
--   sigReduce' (subst' z 0 y) (MkAppChain lhs xs autos nameds) -- TODO: TYPECHECK explicit arguments
-- sigReduce' (IRPi rig AutoImplicit nm x y) 
--           (MkAppChain lhs explicits [] nameds) =
--   case lookup nm nameds of
--       Nothing => throwError ?tr_rhs_12
--       Just av => 
--         sigReduce'
--           (subst' av 0 y)
--           (assert_smaller nameds $ MkAppChain lhs explicits [] $ delete nm nameds)
-- sigReduce' (IRPi rig AutoImplicit nm x y) 
--           (MkAppChain lhs explicits (z :: xs) nameds) = ?tr_rhs_18
-- sigReduce' (IRPi rig (DefImplicit z) nm x y) chain = 
--   case lookup nm chain.nameds of
--     Nothing => assert_total sigReduce' (subst' z 0 y) chain
--     Just av => sigReduce' 
--                 (subst' av 0 y) 
--                 (assert_smaller chain $ {nameds $= delete nm} chain)
-- sigReduce' sig chain = ?tr_rhs_9

