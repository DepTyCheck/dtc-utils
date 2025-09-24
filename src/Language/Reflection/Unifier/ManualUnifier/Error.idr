||| Error management during unification
module Language.Reflection.Unifier.ManualUnifier.Error

import public Language.Reflection.Unifier.ManualUnifier.IR

import public Control.Monad.Error.Interface

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.TTImp

%default total

||| Unification error
public export
data UnificationError =
  ||| Attempting to unify an usupported expression 
  UnsupportedExprTypeError TTImp |
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
  AppNameNotFoundError Name |
  ||| Unifying unsupported pair of types
  UnsupportedUnificationError |
  ||| Attempting to unify non-equal variables
  NEVarsError Name Name |
  ||| Attempting to unify non-equal primitives
  NEPrimitivesError Constant Constant |
  ||| Attempting to unify free variable with bound expression
  UnhandledFvEqBvError | 
  ||| Attempting to unify bound variable with any express that isn't itself
  UnifyingLocalVarError |
  ||| Unifying different apps
  AppUnificationError |
  ||| Failure when unifying lambdas
  LamUnificationError |
  ||| Failure when unifying funcion types
  PiUnificationError |
  ||| Dependency cycle present
  DepCycleError

public export
Show UnificationError where
  show (UnsupportedExprTypeError t) = "UnsupportedExprTypeError \{show t}"
  show (AmbiguousGlobalVarError n ns) = "AmbiguousGlobalVarError {\show n} {\show ns}"
  show (GlobalVarNotFound nm) = "GlobalVarNotFound \{show nm}"
  show (NoNameError _) = "NoNameError"
  show AppReductionError = "AppReductionError"
  show AppBadLhsError = "AppBadLhsError"
  show (AppNameNotFoundError nm) = "AppNameNotFoundError \{show nm}"
  show (UnsupportedUnificationError) = "UnsupportedUnificationError"
  show (NEVarsError nm nm') = "NEVarsError \{show nm} \{show nm'}"
  show (NEPrimitivesError nm nm') = "NEVarsError \{show nm} \{show nm'}"
  show (UnhandledFvEqBvError) = "UnhandledFvEqBvError"
  show (UnifyingLocalVarError) = "UnifyingLocalVarError"
  show (AppUnificationError) = "AppUnificationError"
  show (LamUnificationError) = "LamUnificationError"
  show (PiUnificationError) = "PiUnificationError"
  show (DepCycleError) = "DepCycleError"

public export
||| Fetch error location if possible
errFC : UnificationError -> Maybe FC
errFC (UnsupportedExprTypeError tt) = Just $ getFC tt
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
