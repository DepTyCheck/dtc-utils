||| Definitions for the IR used during unification 
||| and operations on it that don't require a context.
module Language.Reflection.Unification3.IR

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp

import Data.Fin
import Data.Nat
import Data.Vect
import Data.Vect.Views

public export
Foldable PiInfo where
  foldr f acc (DefImplicit x) = f x acc
  foldr f acc _ = acc

public export
Traversable PiInfo where
  traverse f ImplicitArg = pure $ ImplicitArg
  traverse f ExplicitArg = pure $ ExplicitArg
  traverse f AutoImplicit = pure $ AutoImplicit
  traverse f (DefImplicit y) = DefImplicit <$> f y

||| The basic building block of the IR
||| @ vs  amount of free variables
||| @ bjn upper bound on the de bruijn index of bound variables
public export
data IRTerm : (vs : Nat) -> (bjn : Nat) -> Type where
  IRFreeVar   :  Fin vs -> IRTerm vs bjn
  IRLocalVar  : Fin bjn -> IRTerm vs bjn
  IRGlobalVar : Name -> IRTerm vs bjn

  IRType      : IRTerm vs bjn
  IRApp       : IRTerm vs bjn ->         IRTerm vs bjn -> IRTerm vs bjn
  IRAutoApp   : IRTerm vs bjn ->         IRTerm vs bjn -> IRTerm vs bjn
  IRNamedApp  : IRTerm vs bjn -> Name -> IRTerm vs bjn -> IRTerm vs bjn

  IRLam       : Count -> PiInfo (IRTerm vs bjn) -> 
                Name -> IRTerm vs bjn -> 
                IRTerm vs (S bjn) -> IRTerm vs bjn
  IRPi        : Count -> PiInfo (IRTerm vs bjn) -> 
                Name -> IRTerm vs bjn -> 
                IRTerm vs (S bjn) -> IRTerm vs bjn

  IRLet       : Count -> Name -> 
                (type: IRTerm vs bjn) -> 
                (val: IRTerm vs bjn) -> 
                (body: IRTerm vs (S bjn)) -> 
                IRTerm vs bjn

  IRPrim      : Constant -> IRTerm vs bjn

public export
Eq (IRTerm vs bjn)

pinfoEq : PiInfo (IRTerm vs bjn) -> PiInfo (IRTerm vs bjn) -> Bool
pinfoEq ImplicitArg ImplicitArg = True
pinfoEq ExplicitArg ExplicitArg = True
pinfoEq AutoImplicit AutoImplicit = True
pinfoEq (DefImplicit x) (DefImplicit x') = x == x'
pinfoEq _ _ = False

public export
Eq (IRTerm vs bjn) where
  (==) (IRFreeVar x) (IRFreeVar x') = x == x'
  (==) (IRLocalVar x) (IRLocalVar x') = x == x'
  (==) (IRGlobalVar nm) (IRGlobalVar nm') = nm == nm'
  (==) IRType IRType = True
  (==) (IRApp x y) (IRApp x' y') = x == x' && y == y'
  (==) (IRAutoApp x y) (IRAutoApp x' y') = x == x' && y == y'
  (==) (IRNamedApp x nm y) (IRNamedApp x' nm' y') = 
    x == x' && y == y' && nm == nm'
  (==) (IRLam rig pinfo nm x y) (IRLam rig' pinfo' nm' x' y') = 
    rig == rig' && (assert_total pinfoEq pinfo pinfo') && nm == nm' && x == x' && y == y'
  (==) (IRPi rig pinfo nm x y) (IRPi rig' pinfo' nm' x' y') = 
    rig == rig' && (assert_total pinfoEq pinfo pinfo') && nm == nm' && x == x' && y == y'
  (==) (IRLet rig nm type val body) (IRLet rig' nm' type' val' body') = 
    rig == rig' && nm == nm' && type == type' && val == val' && body == body'
  (==) (IRPrim c) (IRPrim c') = c == c'
  (==) _ _ = False

Show Count where
  show M0 = "0 "
  show M1 = "1 "
  show MW = ""

public export
Show (IRTerm vs bjn) where
  show (IRFreeVar x) = "f\{show x}"
  show (IRLocalVar x) = "_\{show x}"
  show (IRGlobalVar nm) = show nm
  show IRType = "Type"
  show (IRApp x y) = "\{show x} \{show y}"
  show (IRAutoApp x y) = "\{show x} @{\{show y}}"
  show (IRNamedApp x nm y) = "\{show x} {\{show nm}=\{show y}}"
  show (IRLam count pinfo nm x y) = "(\\ \{show count}\{show x} => \{show y})"
  show (IRPi count pinfo nm x y) = "(\{show count}\{show x}) -> \{show y}"
  show (IRLet count nm x y z) = 
    "let \{show count}\{show y} : \{show x} in \{show z}"
  show (IRPrim c) = show c

||| Raise the amount of free variables in a term by one
||| TODO: Implement raiseVsN for raising by more than one
public export
raiseVs : IRTerm vs bs -> IRTerm (S vs) bs
raiseVs (IRFreeVar x) = IRFreeVar $ shift 1 x
raiseVs (IRLocalVar x) = IRLocalVar x
raiseVs (IRGlobalVar nm) = IRGlobalVar nm
raiseVs IRType = IRType
raiseVs (IRApp x y) = IRApp (raiseVs x) (raiseVs y)
raiseVs (IRAutoApp x y) = IRAutoApp (raiseVs x) (raiseVs y)
raiseVs (IRNamedApp x nm y) = IRNamedApp (raiseVs x) nm (raiseVs y)
raiseVs (IRLam rig pinfo nm x y) = 
  IRLam rig (raiseVs <$> pinfo) nm (raiseVs x) (raiseVs y)
raiseVs (IRPi rig pinfo nm x y) = 
  IRPi rig (raiseVs <$> pinfo) nm (raiseVs x) (raiseVs y)
raiseVs (IRLet rig nm x y z) = 
  IRLet rig nm (raiseVs x) (raiseVs y) (raiseVs z)
raiseVs (IRPrim c) = IRPrim c

||| Like `Data.Fin.shift`, but the sum in signature is backwards
public export
shift' : (a : Nat) -> Fin b -> Fin (b + a)
shift' x y = rewrite__impl Fin (plusCommutative b x) (shift x y)

||| Raise the expression's bjn number
public export
raise : (i : Nat) -> IRTerm vs bjn -> IRTerm vs (bjn + i)
raise = go 0
  where
  go : {0 bjn : Nat} -> Nat -> (i : Nat) -> IRTerm vs bjn -> IRTerm vs (bjn + i)
  go lower i (IRFreeVar id)           = IRFreeVar id
  go lower i (IRLocalVar j)           = if i > lower 
                                          then IRLocalVar (shift' i j) 
                                          else IRLocalVar (weakenN i j)
  go lower i (IRGlobalVar gn)         = IRGlobalVar gn
  go lower i IRType                   = IRType
  go lower i (IRApp l r)              = IRApp      (go lower i l) (go lower i r)
  go lower i (IRAutoApp l r)          = IRAutoApp  (go lower i l) (go lower i r)
  go lower i (IRNamedApp l nm r)      = IRNamedApp (go lower i l) nm 
                                                   (go lower i r)
  go lower i (IRLam rig pinfo nm tp body) = IRLam  rig (go lower i <$> pinfo) nm 
                                                   (go lower i tp) 
                                                   (go (S lower) i body)
  go lower i (IRPi rig pinfo nm tp body)  = IRPi   rig (go lower i <$> pinfo) nm 
                                                   (go lower i tp) 
                                                   (go (S lower) i body)
  go lower i (IRLet rig nm nTy nVal inner) = IRLet rig nm  (go lower i nTy)
                                                   (go lower i nVal)
                                                   (go (S lower) i inner)
  go lower i (IRPrim c)               = IRPrim c

||| The same as `raise`, but with inverted sum in signature
public export
raise' : (i : Nat) -> IRTerm vs bjn -> IRTerm vs (i + bjn)
raise' i term = rewrite plusCommutative i bjn in raise i term

-- TODO: document this!
newJ : (i : Fin (S bjn)) -> 
       (j : Fin (S bjn)) -> 
       equalNat (finToNat i) (finToNat j) = False -> 
       Fin bjn
newJ FZ          (FS x) p = x
newJ (FS FZ)     FZ p = FZ
newJ (FS (FS x)) FZ p = FZ
newJ (FS FZ)     (FS y) p = FS $ newJ FZ y p
newJ (FS (FS x)) (FS y) p = FS $ newJ (FS x) y p

||| Substitute a bound variable for a term in an expression
||| @ new  the term to substitute with
||| @ at   the variable to subsitute
||| @ term the term in which substitution occurs
public export
subst' : (new : IRTerm vs bjn) -> 
         (at : Fin (S bjn)) -> 
         (into : IRTerm vs (S bjn)) -> 
         IRTerm vs bjn 
subst' new i (IRFreeVar id) = IRFreeVar id
subst' new i (IRLocalVar j) with (i == j) proof p
  subst' new i (IRLocalVar j) | True =  new
  subst' new i (IRLocalVar j) | False = IRLocalVar $ newJ i j p
subst' new i (IRGlobalVar gn) = IRGlobalVar gn
subst' new i IRType = IRType
subst' new i (IRApp l r) = IRApp (subst' new i l) (subst' new i r)
subst' new i (IRAutoApp l r) = IRAutoApp (subst' new i l) (subst' new i r)
subst' new i (IRNamedApp l nm r) = 
  IRNamedApp (subst' new i l) nm (subst' new i r)
subst' new i (IRLam rig pinfo nm tp body) = 
  IRLam rig (subst' new i <$> pinfo) nm (subst' new i tp) 
            (subst' (raise' 1 new) (shift 1 i) body)
subst' new i (IRPi rig pinfo nm tp body) = 
  IRPi rig (subst' new i <$> pinfo) nm (subst' new i tp) 
           (subst' (raise' 1 new) (shift 1 i) body)
subst' new i (IRLet rig nm nTy nVal inner) = 
  IRLet rig nm (subst' new i nTy) (subst' new i nVal) 
               (subst' (raise' 1 new) (shift 1 i) inner)
subst' new i (IRPrim c) = IRPrim c

helpPi : (a -> Bool) -> PiInfo a -> Bool
helpPi f (DefImplicit x) = f x
helpPi f _ = False

public export
isClosed : IRTerm vs bjn -> Bool
isClosed (IRFreeVar _) = False
isClosed (IRLocalVar _) = True
isClosed (IRGlobalVar _) = ?gv_closed
isClosed IRType = True
isClosed (IRApp l r) = isClosed l && isClosed r
isClosed (IRAutoApp l r) = isClosed l && isClosed r
isClosed (IRNamedApp l _ r) = isClosed l && isClosed r
isClosed (IRLam rig pi _ tp body) = 
  helpPi isClosed pi && isClosed tp && isClosed body
isClosed (IRPi rig pi _ tp body) = 
  helpPi isClosed pi && isClosed tp && isClosed body
isClosed (IRLet rig _ nT nV inner) = 
  isClosed nT && isClosed nV && isClosed inner
isClosed (IRPrim c) = True

public export
mapAIR' : Applicative m => 
          (f : {0 bjn' : Nat} -> 
               (original : IRTerm vs bjn') -> 
               m (IRTerm vs bjn') -> 
               m (IRTerm vs bjn')) -> 
          IRTerm vs bjn -> 
          m (IRTerm vs bjn)
mapAIR' f t@(IRFreeVar x) = f t (pure t) 
mapAIR' f t@(IRLocalVar x) = f t (pure t) 
mapAIR' f t@(IRGlobalVar nm) = f t (pure t)
mapAIR' f t@IRType = f t (pure t)
mapAIR' f t@(IRApp x y) = f t $ IRApp <$> mapAIR' f x <*> mapAIR' f y
mapAIR' f t@(IRAutoApp x y) = 
  f t $ IRAutoApp <$> mapAIR' f x <*> mapAIR' f y
mapAIR' f t@(IRNamedApp x nm y) = 
  f t $ IRNamedApp <$> mapAIR' f x <*> pure nm <*> mapAIR' f y
mapAIR' f t@(IRLam rig pinfo nm x y) = 
  f t $ IRLam rig <$> traverse (mapAIR' f) pinfo <*> pure nm <*> mapAIR' f x <*> mapAIR' f y
mapAIR' f t@(IRPi rig pinfo nm x y) = 
  f t $ IRPi rig <$> traverse (mapAIR' f) pinfo <*> pure nm <*> mapAIR' f x <*> mapAIR' f y
mapAIR' f t@(IRLet rig nm type val body) = 
  f t $ IRLet rig nm <$> mapAIR' f type <*> mapAIR' f val <*> mapAIR' f body
mapAIR' f t@(IRPrim c) =  f t (pure t)

public export %inline
mapAIR : Applicative m => 
         (f : {0 bjn' : Nat} -> m (IRTerm vs bjn') -> m (IRTerm vs bjn')) ->
         IRTerm vs bjn ->
         m (IRTerm vs bjn)
mapAIR f t = mapAIR' (\_ => f) t

public export %inline
mapMIR' : Monad m => 
         (f : {0 bjn' : Nat} -> 
              (original: IRTerm vs bjn') -> 
              (mapped : IRTerm vs bjn') -> 
              m (IRTerm vs bjn')) ->
         IRTerm vs bjn ->
         m (IRTerm vs bjn)
mapMIR' f t = mapAIR' (\o, m => m >>= f o) t

public export %inline
mapMIR : Monad m => 
         (f : {0 bjn' : Nat} -> 
              (mapped : IRTerm vs bjn') -> 
              m (IRTerm vs bjn')) ->
         IRTerm vs bjn ->
         m (IRTerm vs bjn)
mapMIR f t = mapAIR' (\_, m => m >>= f) t

