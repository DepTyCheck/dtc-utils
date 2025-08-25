module Language.Reflection.Unification3.Error

import public Language.Reflection.Unification3.IR

import public Control.Monad.Error.Interface

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.TTImp

%default total

||| Unification error
public export
data UnificationError =
  ||| Attempting to unify an usupported expression 
  UnsupportedExprTypeError FC |
  ||| A global variable is ambiguous.
  AmbiguousGlobalVarError Name (List Name) |
  ||| Global variable not found
  GlobalVarNotFound Name |
  ||| Attempting to unify a lambda or pi with an unnamed parameter
  |||
  ||| This should not occur when unifying expressions provided by 
  ||| the Elab monad, since unnamed parameters receive machine-generated "names"
  NoNameError FC |
  ||| Error when reducing IApp
  AppReductionError |
  ||| Left-hand side of a function application expression is not a function
  AppBadLhsError | 
  ||| Didn't find an appropriately named argument value during reduction
  AppNameNotFoundError

public export
Show UnificationError where
  show (UnsupportedExprTypeError _) = "UnsupportedExprTypeError"
  show (AmbiguousGlobalVarError n ns) = "AmbiguousGlobalVarError {\show n} {\show ns}"
  show (GlobalVarNotFound nm) = "GlobalVarNotFound \{show nm}"
  show (NoNameError _) = "NoNameError"
  show AppReductionError = "AppReductionError"
  show AppBadLhsError = "AppBadLhsError"
  show AppNameNotFoundError = "AppNameNotFoundError"

public export
||| Fetch error location if possible
errFC : UnificationError -> Maybe FC
errFC (UnsupportedExprTypeError fc) = Just fc
errFC (NoNameError fc) = Just fc
errFC _ = Nothing

public export
warnBecause : UnificationError -> Elab ()
warnBecause ue =
  case errFC ue of
       Just fc => warnAt fc "Unification failed: \{show ue}"
       Nothing => warn "Unification failed: \{show ue}"

public export
failBecause : UnificationError -> Elab ()
failBecause ue = 
  case errFC ue of
       Just fc => failAt fc "Unification failed: \{show ue}"
       Nothing => warn "Unification failed: \{show ue}"
