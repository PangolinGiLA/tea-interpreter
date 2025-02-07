module VMTypes where

import Data.Map

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

import Syntax.Abs (Type(..), TComp(..))

-- The Monad --

-- Monad functionalities:

-- Reader:
--  - ask :: m env,
--  - reader :: (env -> a) -> m a           [get some component of env]
--  - local :: (env -> env) -> m a -> m a   [transformation -> instruction -> result]

-- Writer:
--  - tell :: msg -> m ()

-- Except:
--  - throwError :: err -> m a,
--  - catchError :: m a -> (err -> m a) -> m a

-- State:
--  - get :: m sto
--  - gets :: (sto -> a) -> m a          [get some component of sto]
--  - put :: sto -> m ()
--  - modify :: (sto -> sto) -> m ()
--                                       [modify f = do { x <- get; put (f x) }]

---- Virtual machine (VM) monad unwrapped ----
-- m (Either DiffCFlow a)                               ; <- ExceptT
-- m ((Either DiffCFlow a), [Log])                      ; <- WriterT
-- Env -> m ((Either DiffCFlow a), [Log])               ; <- ReaderT
-- Env -> Store -> (((Either DiffCFlow a), [Log]), Store)   ; <- StateT ... Identity

type VM a = ExceptT DiffCFlow (WriterT [Log] (ReaderT Env (StateT Store Identity))) a

-- Control flow utils --
-- Different control flow (either an error or a return flag).
-- Note: function's semantics must include catching a "different control flow"
-- event and checking if it is a return value (otherwise rethrowing it).
-- If return value is not caught after the end of the program, a special error
-- is emitted.
type DiffCFlow = Either Error RetVal
-- Return value (can be void).
type RetVal = Value

-- Diagnostics --
type CodePos = (Int, Int)
data Diag = Err Error | Warn Warning
-- Err: can only happen once, returned as (Left Err, Log) from the program
-- and logged to Log.
data Error
    = DivZero
    | ModZero
    | UseUninit Loc
    | Undeclared CodePos String
    | CharOutOfBounds Integer
    | ArrOutOfBounds Integer Integer -- idx, len
    | PopEmpty CodePos String -- pos, arrName
    | NegativeSize CodePos String -- pos, arrName
    | AssertionFailed String -- message
    | UncaughtReturnValue Value
    | PanicUnexpectedType

-- Warning: can happen multiple times, logged to Log.
data Warning
    = IntLoss IntLossReason Integer Integer -- reason, before, after

data IntLossReason = Conversion | Arithmetic | Literal

-- Streams --
-- Log is always returned by the program regardless of any errors.
-- Stdout: output of print().
-- Stderr: output of diagnostics (warnings and errors).
data Log = Stdout String | Stderr Diag

-- Data types --
data Value
    = Vint (Integer, IntVariety)
    | Vvoid
    | Vbool Bool
    | Vchar Char
    | Vstr String
    | Varr [Value] -- < eq types   | <- both asserted
    | Vtup [Value] -- < const len  |    during type-checking
    | Vfun (Value -> VM Value)
    | Ref Loc
-- Note: named references (as in `let x = ref y`) are values (unlike in Tiny!).
-- That way assignment to a reference can be a statement (it doesn't modify
-- the environment).
-- 
-- Constness only matters during type-checking and is not included
-- in values.

data IntVariety = I32 | I64 | U32 | U64

-- Internal memory structure --
type Var = String
type TypeVar = String
type Loc = Integer

-- Variable environment for locations.
type VEnv = Map Var Loc
-- Type environment for aliases.
-- Note that const or ref types cannot be aliased, thus TComp.
-- Beware! This map is completely flat as Talias is not in TComp.
-- This environment is necessary during interpretation, because,
-- in our language, casts between integers can mutate State.
type TEnv = Map TypeVar TComp
-- Compound environment storing both variable environment
-- and type environment.
data Env = CEnv {varEnv :: VEnv, typeEnv :: TEnv}
data Store = CStore {currMap :: Map Loc Value, nextLoc :: Loc}
