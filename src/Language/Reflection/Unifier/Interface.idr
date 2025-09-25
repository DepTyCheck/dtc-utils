module Language.Reflection.Unifier.Interface

import public Control.Monad.Either
import public Data.Either
import public Data.FinBitSet
import public Data.SortedMap
import public Data.Vect
import public Decidable.Equality
import public Language.Reflection
import public Language.Reflection.Syntax

public export
record UnificationTask where
  constructor MkUniTask
  lfv : Nat
  lhsFreeVars : Vect lfv (Name, TTImp)
  lhs : TTImp
  rfv : Nat
  rhsFreeVars : Vect rfv (Name, TTImp)
  rhs : TTImp

%name UnificationTask task

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

%name FVData fv, fvData

public export
Eq FVData where
  (==) (MkFVData n h t v) (MkFVData n' h' t' v') = 
    n == n' && h == h' && t == t' && v == v'

public export
Show FVData where
  show (MkFVData n h t v) = "MkFVData \{show n} \{h} (\{show t}) (\{show v})"

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

%name DependencyGraph dg, depGraph

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

prettyDeps : (dg : DependencyGraph) -> FinBitSet dg.freeVars -> String
prettyDeps dg deps = 
  if deps == empty then
    ""
  else
    " Depends on: \{show $ (name . flip index dg.fvData) <$> toList deps}\n"

prettyFV : (dg : DependencyGraph) -> FVData -> String
prettyFV dg fvd = 
  "\{show fvd.name} : \{show fvd.type}" ++ 
    (case fvd.value of
      Nothing => "\n"
      Just val => " = \{show val}\n") ++
    " n2Id : \{show $ lookup fvd.name dg.nameToId}; " ++
    " h2Id : \{show $ lookup fvd.holeName dg.holeToId}\n"


public export
prettyDG : DependencyGraph -> String
prettyDG dg = 
  "\{show dg.freeVars} free variables:\n" ++ 
    (joinBy "" $ 
      (\(a,b) => prettyFV dg a ++ prettyDeps dg b) <$> 
        (toList $ zip dg.fvData dg.fvDeps)) ++
    "===\nEmpties: \{show $ (name . flip index dg.fvData) <$> toList dg.empties}\n======"

public export
printDG : (Either String DependencyGraph) -> IO ()
printDG = putStrLn . fromMaybe "" . eitherToMaybe . map prettyDG

public export
Unifier : Type
Unifier = UnificationTask -> Elab $ Either String DependencyGraph

