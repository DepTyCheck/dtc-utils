module Language.Reflection.Unification3.Context.Main

import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.State

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.Error

import public Data.Fin
import public Data.SortedMap

%default total

||| List of free variables in expression
||| @ fvs amount of free variables
public export
data FreeVars : (fvs : Nat) -> Type where
  Lin  : FreeVars 0
  (:<) : FreeVars fvs -> (Name, IRTerm fvs 0) -> FreeVars (S fvs)

public export
Show (FreeVars fvs)

show_inner : FreeVars fvs -> String
show_inner [<] = "[<"
show_inner ([<] :< x) = "[< x"
show_inner (xs :< x) = "\{show xs}, \{show x}"

public export
Show (FreeVars fvs) where
  show f = "\{show_inner f}]"

namespace FreeVars
  ||| Get a free variable's name and type by its de Bruijn index
  public export
  index : Fin fvs -> FreeVars fvs -> (Name, IRTerm fvs 0)
  index FZ     (x :< (y, z)) = (y, raiseVs z)
  index (FS x) (y :< z)      = mapSnd raiseVs $ index x y

||| Find the index of a free varible by its name
public export
queryFV : Name -> FreeVars fvs -> Maybe $ Fin fvs
queryFV nm [<] = Nothing
queryFV nm (xs :< (nm', x)) = if nm == nm' 
                                 then Just 0 
                                 else shift 1 <$> queryFV nm xs

||| Find the name of a free variable by its index
public export
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

  public export
  Show (BoundNames bjn)

  public export
  show_inner : BoundNames bjn -> String
  show_inner [<] = "[<"
  show_inner ([<] :< x) = "[< x"
  show_inner (xs :< x) = "\{show xs}, \{show x}"

  public export
  Show (BoundNames bjn) where
    show f = "\{show_inner f}]"

||| Find the index of a bound variable by its name
public export
queryBN : Name -> BoundNames bjn -> Maybe $ Fin bjn
queryBN nm [<] = Nothing
queryBN nm (xs :< nm') = 
  if nm == nm' 
     then Just 0 
     else shift 1 <$> queryBN nm xs

||| Find the name of a bound variable by its index
public export
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

  public export
  Show (BoundVars fvs bjn)

  show_inner : BoundVars fvs bjn -> String
  show_inner [<] = "[<"
  show_inner ([<] :< x) = "[< x"
  show_inner (xs :< x) = "\{show xs}, \{show x}"

  public export
  Show (BoundVars fvs bjn) where
    show f = "\{show_inner f}]"

  public export
  Eq (BoundVars fvs bjn) where
    (==) Lin Lin = True
    (==) (x :< y) (x' :< y') = x == x && y == y
    (==) _ _ = False

public export
||| Find the index of a bound variable by its name
queryBV : Name -> BoundVars fvs bjn -> Maybe $ Fin bjn
queryBV nm [<] = Nothing
queryBV nm (xs :< (nm', t)) =
  if nm == nm'
     then Just 0
     else shift 1 <$> queryBV nm xs

public export
||| Find the name of a bound variable by its index
boundVarName : Fin bjn -> BoundVars fvs bjn -> Name
boundVarName FZ (x :< (y, t)) = y
boundVarName (FS x) (y :< _) = boundVarName x y


