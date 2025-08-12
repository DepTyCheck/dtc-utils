module Language.Reflection.Unification3.Error

import Language.Reflection.Unification3.IR

import Control.Monad.Error.Interface

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp

||| Unification error
public export
data UnificationError =
  ||| Attempting to unify an expression 
  UnsupportedExprTypeError FC |
  ||| Attempting to unify a lambda or pi with an unnamed parameter
  |||
  ||| This should not occur when unifying expressions provided by 
  ||| the Elab monad, since unnamed parameters receive machine-generated "names"
  NoNameError FC |
  ||| Error when reducing IApp
  AppReductionError

public export
Show UnificationError where
  show (UnsupportedExprTypeError _) = "UnsupportedExprTypeError"
  show (NoNameError _) = "NoNameError"
  show AppReductionError = "AppReductionError"

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
