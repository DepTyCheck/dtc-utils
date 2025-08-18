module Language.Reflection.Logging

import Language.Reflection
import Control.Monad.Identity

public export 
interface Monad m => MonadLog m where
  logMsg' : String -> Nat -> String -> m ()
  logTerm' : String -> Nat -> String -> TTImp -> m ()

public export
Elaboration m => MonadLog m where
  logMsg' = logMsg
  logTerm' = logTerm

public export
MonadLog Identity where
  logMsg' _ _ _ = pure ()
  logTerm' _ _ _ _ = pure ()
