module VMUtils where
import VMTypes

import Data.Map (empty)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

initialEnv :: Env
initialEnv = CEnv { varEnv = Data.Map.empty, typeEnv = Data.Map.empty }

initialStore :: Store
initialStore = CStore { currMap = Data.Map.empty, nextLoc = 0 }

runVM :: VM a -> Env -> Store -> ((Either DiffCFlow a, [Log]), Store)
runVM vm env store = runIdentity $ runStateT (runReaderT (runWriterT (runExceptT vm)) env) store