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
typeof freeVars boundVars globalVars (IRFreeVar x) = pure $ raise bjn $ snd $ index x freeVars
typeof freeVars boundVars globalVars (IRLocalVar x) = pure $ snd $ index x boundVars
typeof freeVars boundVars globalVars (IRGlobalVar nm) = 
  case lookup nm globalVars of
    Just (t, _) => pure $ raise bjn t
    Nothing => throwError $ GlobalVarNotFound nm
typeof freeVars boundVars globalVars IRType = pure IRType
typeof freeVars boundVars globalVars (IRApp x y) = ?typeof_app
typeof freeVars boundVars globalVars (IRAutoApp x y) = ?typeof_auto
typeof freeVars boundVars globalVars (IRNamedApp x nm y) = ?typeof_namedj
typeof freeVars boundVars globalVars (IRLam rig pinfo nm x y) = 
  IRPi rig pinfo nm x <$> typeof freeVars (boundVars :< (nm, x)) globalVars y
typeof freeVars boundVars globalVars (IRPi rig pinfo nm x y) = pure IRType
typeof freeVars boundVars globalVars (IRLet rig nm x y z) = 
  typeof freeVars boundVars globalVars (subst' y 0 z)
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

-- TODO: Typechecking!
appReduce : MonadError UnificationError m => 
            (lhs : IRTerm fvs bjn) -> (rhs: IRTerm fvs bjn) -> m (IRTerm fvs bjn)
appReduce (IRLam _ ExplicitArg _ ty body) rhs = pure $ subst' rhs 0 body
appReduce (IRLam rig pinfo nm ty body) rhs = IRLam rig pinfo nm ty <$> appReduce body (raise' 1 rhs)
-- appReduce (IRApp _ _) rhs = throwError AppReductionError
appReduce IRType rhs = throwError AppReductionError
appReduce (IRPi _ _ _ _ _) rhs = throwError AppReductionError
appReduce (IRPrim _) rhs = throwError AppReductionError
appReduce lhs rhs = pure $ IRApp lhs rhs

autoAppReduce : MonadError UnificationError m => 
                (lhs : IRTerm fvs bjn) -> (rhs : IRTerm fvs bjn) -> m (IRTerm fvs bjn)
autoAppReduce (IRLam _ AutoImplicit _ ty body) rhs = pure $ subst' rhs 0 body
autoAppReduce (IRLam rig pinfo nm ty body) rhs = IRLam rig pinfo nm ty <$> autoAppReduce body (raise' 1 rhs)
autoAppReduce IRType rhs = throwError AppReductionError
autoAppReduce (IRPi _ _ _ _ _) rhs = throwError AppReductionError
autoAppReduce (IRPrim _) rhs = throwError AppReductionError
autoAppReduce lhs rhs = pure $ IRAutoApp lhs rhs

namedAppReduce : MonadError UnificationError m => 
                 (lhs : IRTerm fvs bjn) -> Name -> (rhs : IRTerm fvs bjn) -> m (IRTerm fvs bjn)
namedAppReduce (IRLam rig pinfo nm ty body) nm' rhs = 
  if nm == nm' 
     then pure $ subst' rhs 0 body 
     else IRLam rig pinfo nm ty <$> namedAppReduce body nm' (raise' 1 rhs)
namedAppReduce IRType nm rhs = throwError AppReductionError
namedAppReduce (IRPi _ _ _ _ _) nm rhs = throwError AppReductionError
namedAppReduce (IRPrim _) nm rhs = throwError AppReductionError
namedAppReduce lhs nm rhs = pure $ IRNamedApp lhs nm rhs

reduce (IRFreeVar id) = pure $ IRFreeVar id
reduce (IRLocalVar id) = pure $ IRLocalVar id
reduce (IRGlobalVar gn) = pure $ IRGlobalVar gn
reduce IRType = pure $ IRType
reduce (IRApp l r) = appReduce !(reduce l) !(reduce r)
reduce (IRAutoApp l r) = autoAppReduce !(reduce l) !(reduce r)
reduce (IRNamedApp l nm r) = namedAppReduce !(reduce l) nm !(reduce r)
reduce (IRLam rig pinfo nm ty body) =
  pure $ IRLam rig !(traverse reduce pinfo) nm !(reduce ty) !(reduce body)
reduce (IRPi rig pinfo nm ty body) = 
  pure $ IRPi rig !(traverse reduce pinfo) nm !(reduce ty) !(reduce body)
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
  go : IRTerm fvs bjn -> List (IRAppArg fvs bjn) -> (IRTerm fvs bjn, List $ IRAppArg fvs bjn)
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
toAC (MkAppChain' lhs explicits autos nameds) = MkAppChain lhs (toList explicits) (toList autos) nameds

sigReduce : MonadError UnificationError m => IRTerm fvs bjn -> AppChain fvs bjn -> m $ IRTerm fvs bjn
sigReduce (IRPi rig ImplicitArg nm x y) chain = 
  case lookup nm chain.nameds of
    Nothing => throwError ?tr_rhs_10
    Just av => sigReduce (subst' av 0 y) ({nameds $= delete nm} chain) -- TODO: unify types when applying.
sigReduce (IRPi rig ExplicitArg nm x y) (MkAppChain lhs [] autos nameds) = ?tr_rhs_15
sigReduce (IRPi rig ExplicitArg nm x y) (MkAppChain lhs (z :: xs) autos nameds) = ?tr_rhs_16
sigReduce (IRPi rig AutoImplicit nm x y) (MkAppChain lhs explicits [] nameds) = ?tr_rhs_17
sigReduce (IRPi rig AutoImplicit nm x y) (MkAppChain lhs explicits (z :: xs) nameds) = ?tr_rhs_18
sigReduce (IRPi rig (DefImplicit z) nm x y) chain = ?tr_rhs_13
sigReduce sig chain = ?tr_rhs_9

