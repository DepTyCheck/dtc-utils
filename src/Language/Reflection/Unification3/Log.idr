||| Unifier logging infrastructure
module Language.Reflection.Unification3.Log

import public Language.Reflection
import public Control.Monad.Writer

public export
interface Monad m => MonadLog m where
  logStr : Nat -> String -> m ()
  logTerm' : Nat -> String -> TTImp -> m ()
  logSTerm' : Nat -> String -> TTImp -> m ()

public export
[logElab] Elaboration m => MonadLog m where
  logStr n s = logMsg "unifier" n s
  logTerm' n s t = logTerm "unifier" n s t
  logSTerm' n s t = logSugaredTerm "unifier" n s t

public export
[logWriter] (MonadWriter (List String) m) => MonadLog m where
  logStr n s = tell $ singleton "\{show n} \{s}"
  logTerm' n s t = tell $ singleton "\{show n} \{s}: \{show t}"
  logSTerm' n s t = tell $ singleton "\{show n} \{s}: \{show t}"
