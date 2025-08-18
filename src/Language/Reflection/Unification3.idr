module Language.Reflection.Unification3

import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.Error

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

||| List of free variables in expression
||| @ fvs amount of free variables
public export
data FreeVars : (fvs : Nat) -> Type where
  Lin  : FreeVars 0
  (:<) : FreeVars fvs -> (Name, IRTerm fvs 0) -> FreeVars (S fvs)

namespace FreeVars
  ||| Get a free variable's name and type by its de Bruijn index
  public export
  index : Fin fvs -> FreeVars fvs -> (Name, IRTerm fvs 0)
  index FZ     (x :< (y, z)) = (y, raiseVs z)
  index (FS x) (y :< z)      = mapSnd raiseVs $ index x y

||| Find the index of a free varible by its name
queryFV : Name -> FreeVars fvs -> Maybe $ Fin fvs
queryFV nm [<] = Nothing
queryFV nm (xs :< (nm', x)) = if nm == nm' 
                                 then Just 0 
                                 else shift 1 <$> queryFV nm xs

||| Find the name of a free variable by its index
freeVarName : Fin fvs -> FreeVars fvs -> Name
freeVarName FZ     (x :< y) = fst y
freeVarName (FS x) (y :< z) = freeVarName x y

||| List of bound variable names in expression
||| @ bjn upper bound on bound variable de Bruijn index
namespace BoundNames
  public export
  data BoundNames : (bjn : Nat) -> Type where
    Lin  : BoundNames 0
    (:<) : BoundNames bjn -> Name -> BoundNames (S bjn)

||| Find the index of a bound variable by its name
queryBN : Name -> BoundNames bjn -> Maybe $ Fin bjn
queryBN nm [<] = Nothing
queryBN nm (xs :< nm') = 
  if nm == nm' 
     then Just 0 
     else shift 1 <$> queryBN nm xs

||| Find the name of a bound variable by its index
boundName : Fin bjn -> BoundNames bjn -> Name
boundName FZ (x :< y) = y
boundName (FS x) (y :< z) = boundName x y

namespace BoundVars
  ||| List of bound variables in expression (with types)
  public export
  data BoundVars : (fvs : Nat) -> (bjn : Nat) -> Type where
    Lin : BoundVars fvs 0
    (:<) : BoundVars fvs bjn -> (Name, IRTerm fvs bjn) -> BoundVars fvs (S bjn)

  ||| Find a bound variable by its index
  public export
  index : Fin bjn -> BoundVars fvs bjn -> (Name, IRTerm fvs bjn)
  index FZ (x :< y) = mapSnd (raise' 1) y
  index (FS x) (y :< z) = mapSnd (raise' 1) $ index x y

||| Find the index of a bound variable by its name
queryBV : Name -> BoundVars fvs bjn -> Maybe $ Fin bjn
queryBV nm [<] = Nothing
queryBV nm (xs :< (nm', t)) =
  if nm == nm'
     then Just 0
     else shift 1 <$> queryBV nm xs

||| Find the name of a bound variable by its index
boundVarName : Fin bjn -> BoundVars fvs bjn -> Name
boundVarName FZ (x :< (y, t)) = y
boundVarName (FS x) (y :< _) = boundVarName x y

GlobalVars : (fvs : Nat) -> Type
GlobalVars fvs = SortedMap Name (IRTerm fvs 0, NameType)

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

