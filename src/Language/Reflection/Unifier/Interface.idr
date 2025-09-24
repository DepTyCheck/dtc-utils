module Language.Reflection.Unifier.Interface

import public Control.Monad.Either
import public Data.Vect
import public Data.SortedMap
import public Data.FinBitSet
import public Decidable.Equality
import public Language.Reflection

public export
record UnificationTask where
  constructor MkUniTask
  lfv : Nat
  lhsFreeVars : Vect lfv (Name, TTImp)
  lhs : TTImp
  rfv : Nat
  rhsFreeVars : Vect rfv (Name, TTImp)
  rhs : TTImp

public export
Show UnificationTask where
  show (MkUniTask l lfv lhs r rfv rhs) = 
    "MkUniTask \{show l} \{show lfv} \{show lhs} \{show r} \{show rfv} \{show rhs}"

public export
record FVData where
  constructor MkFVData
  name : Name
  holeName : String
  type : TTImp
  value : Maybe TTImp

public export
Eq FVData where
  (==) (MkFVData n h t v) (MkFVData n' h' t' v') = 
    n == n' && h == h' && t == t' && v == v'

public export
Show FVData where
  show (MkFVData n h t v) = "MkFVData \{show n} \{h} \{show t} \{show v}"

public export
makeFVData : (String, Name, TTImp, Maybe TTImp) -> FVData
makeFVData (h, n, t, v) = MkFVData n h t v

public export
record DependencyGraph where
  constructor MkDG
  freeVars : Nat
  fvData : Vect freeVars FVData
  fvDeps : Vect freeVars $ FinBitSet freeVars
  --- The set of all i: (Fin freeVars), where (index i fvData).value = None
  empties : FinBitSet freeVars
  --- For all i : (Fin freeVars); (lookup (index i fvData).name nameToId) = i
  nameToId : SortedMap Name $ Fin freeVars
  --- For all i : (Fin freeVars); (lookup (index i fvData).holeName holeToId) = i
  holeToId : SortedMap String $ Fin freeVars

public export
Eq DependencyGraph where
  (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') with (decEq a a') 
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | Yes p =
    a == a' && b == (rewrite p in b') && c == (rewrite p in c') && 
      d == (rewrite p in d') && e == (rewrite p in e') && f == (rewrite p in f')
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | No _ = False

public export
Show DependencyGraph where
  show (MkDG a b c d e f) = 
    "MkDG \{show a} \{show b} \{show c} \{show d} \{show e} \{show f}"

public export
Unifier : Type
Unifier = UnificationTask -> Elab $ Either String DependencyGraph

