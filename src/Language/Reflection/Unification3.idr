module Language.Reflection.Unification3

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR

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

public export
reduce : MonadError UnificationError m => IRTerm fvs bjn -> m $ IRTerm fvs bjn

||| Given the context of free and bound variables, determine the type of an expression
public export
typeof : MonadError UnificationError m => 
         {bjn : Nat} -> 
         FreeVars fvs -> 
         BoundVars fvs bjn -> 
         GlobalVars fvs -> 
         IRTerm fvs bjn -> 
         m $ IRTerm fvs bjn
typeof freeVars boundVars globalVars (IRFreeVar x) = 
  pure $ raise bjn $ snd $ index x freeVars
typeof freeVars boundVars globalVars (IRLocalVar x) = 
  pure $ snd $ index x boundVars
typeof freeVars boundVars globalVars (IRGlobalVar nm) = 
  case lookup nm globalVars of
    Just (t, _) => pure $ raise bjn t
    Nothing => throwError $ GlobalVarNotFound nm
typeof freeVars boundVars globalVars IRType = pure IRType
typeof freeVars boundVars globalVars (IRApp x y) = ?typeof_app
typeof freeVars boundVars globalVars (IRAutoApp x y) = ?typeof_auto
typeof freeVars boundVars globalVars (IRNamedApp x nm y) = ?typeof_namedj
typeof freeVars boundVars globalVars (IRLam rig pinfo nm x y) = 
  IRPi rig pinfo nm x <$> 
    assert_total typeof freeVars (boundVars :< (nm, x)) globalVars y
typeof freeVars boundVars globalVars (IRPi rig pinfo nm x y) = pure IRType
typeof freeVars boundVars globalVars (IRLet rig nm x y z) = 
  assert_total typeof freeVars boundVars globalVars (subst' y 0 z)
typeof freeVars boundVars globalVars (IRPrim (I i)) = pure $ IRGlobalVar "Int"
typeof freeVars boundVars globalVars (IRPrim (BI i)) = pure $ IRGlobalVar "Integer"
typeof freeVars boundVars globalVars (IRPrim (I8 i)) = pure $ IRGlobalVar "Int8"
typeof freeVars boundVars globalVars (IRPrim (I16 i)) = pure $ IRGlobalVar "Int16"
typeof freeVars boundVars globalVars (IRPrim (I32 i)) = pure $ IRGlobalVar "Int32"
typeof freeVars boundVars globalVars (IRPrim (I64 i)) = pure $ IRGlobalVar "Int64"
typeof freeVars boundVars globalVars (IRPrim (B8 m)) = pure $ IRGlobalVar "Bits8"
typeof freeVars boundVars globalVars (IRPrim (B16 m)) = pure $ IRGlobalVar "Bits16"
typeof freeVars boundVars globalVars (IRPrim (B32 m)) = pure $ IRGlobalVar "Bits32"
typeof freeVars boundVars globalVars (IRPrim (B64 m)) = pure $ IRGlobalVar "Bits64"
typeof freeVars boundVars globalVars (IRPrim (Str str)) = pure $ IRGlobalVar "String"
typeof freeVars boundVars globalVars (IRPrim (Ch c)) = pure $ IRGlobalVar "Char"
typeof freeVars boundVars globalVars (IRPrim (Db dbl)) = pure $ IRGlobalVar "Double"
typeof freeVars boundVars globalVars (IRPrim (PrT pty)) = pure $ IRGlobalVar "PrimType"
typeof freeVars boundVars globalVars (IRPrim WorldVal) = pure $ IRType

reduce (IRFreeVar id) = pure $ IRFreeVar id
reduce (IRLocalVar id) = pure $ IRLocalVar id
reduce (IRGlobalVar gn) = pure $ IRGlobalVar gn
reduce IRType = pure $ IRType
reduce (IRApp l r) = ?rirapp
reduce (IRAutoApp l r) = ?riraapp
reduce (IRNamedApp l nm r) = ?rirnapp
reduce (IRLam rig pinfo nm ty body) =
  pure $ IRLam rig 
               !(traverse (assert_total reduce) pinfo) 
               nm !(reduce ty) !(reduce body)
reduce (IRPi rig pinfo nm ty body) = 
  pure $ IRPi rig 
               !(traverse (assert_total reduce) pinfo) 
               nm !(reduce ty) !(reduce body)
reduce (IRLet rig nm nTy nVal inner) = pure $ subst' nVal 0 inner
reduce (IRPrim c) = pure $ IRPrim c

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

-- TODO: TYPECHECK THIS!
-- covering
sigReduce' : MonadError UnificationError m => 
            IRTerm fvs bjn -> 
            AppChain fvs bjn -> 
            m $ IRTerm fvs bjn
sigReduce' (IRPi rig ImplicitArg nm x y) chain = 
  case lookup nm chain.nameds of
    Nothing => throwError ?tr_rhs_10
    Just av => sigReduce' 
                (subst' av 0 y) 
                (assert_smaller chain $ {nameds $= delete nm} chain) 
sigReduce' (IRPi rig ExplicitArg nm x y) 
          chain@(MkAppChain lhs [] autos nameds) = 
  case lookup nm nameds of
    Nothing => throwError ?tr_rhs_11
    Just av => 
      sigReduce'
        (subst' av 0 y)
        (assert_smaller nameds $ MkAppChain lhs [] autos $ delete nm nameds)
sigReduce' (IRPi rig ExplicitArg nm x y) 
          (MkAppChain lhs (z :: xs) autos nameds) =
  sigReduce' (subst' z 0 y) (MkAppChain lhs xs autos nameds) -- TODO: TYPECHECK explicit arguments
sigReduce' (IRPi rig AutoImplicit nm x y) 
          (MkAppChain lhs explicits [] nameds) =
  case lookup nm nameds of
      Nothing => throwError ?tr_rhs_12
      Just av => 
        sigReduce'
          (subst' av 0 y)
          (assert_smaller nameds $ MkAppChain lhs explicits [] $ delete nm nameds)
sigReduce' (IRPi rig AutoImplicit nm x y) 
          (MkAppChain lhs explicits (z :: xs) nameds) = ?tr_rhs_18
sigReduce' (IRPi rig (DefImplicit z) nm x y) chain = 
  case lookup nm chain.nameds of
    Nothing => assert_total sigReduce' (subst' z 0 y) chain
    Just av => sigReduce' 
                (subst' av 0 y) 
                (assert_smaller chain $ {nameds $= delete nm} chain)
sigReduce' sig chain = ?tr_rhs_9

