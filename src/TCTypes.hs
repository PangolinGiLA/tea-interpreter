module TCTypes where

import Data.Map

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

import Syntax.Abs (Type(..), TComp(..), TypeNoref, CIdent, TClean)
import VMTypes

type TC a = ExceptT TCError (WriterT [TCDiag] (ReaderT TCEnv Identity)) a

data TCError
    = TypeMismatch Type Type -- expected, provided
    | PlusMismatch Type Type -- provided operands
    | MinusMismatch Type Type -- provided operands
    | ExpectedInteger Type
    | ExpectedSigned Type
    | ExpectedOrdering Type
    | ExpectedArr Type
    | SizeIsI64 Type
    | ExpectedFun Type
    | InvalidTupleSize
    | TupleUnpackingMismatch
    | UnpackedRefTuple Type
    | UndeclaredVar CodePos String
    | UndeclaredAlias CodePos String
    | AliasShadowing CodePos String
    | ConstViolation Type
    | InvalidCast Type Type -- to, from
    | UncaughtReturn
    | NoReturn
    | UninitRef Type
    | ArrayLvalue
    | EmptyArray
    | DifferentArrayTypes

data TCWarning
    = Shadowing CodePos String
    | UnusedReturn CodePos String
    | DeadCode

data TCDiag = TCErr TCError | TCWarn TCWarning

-- Variable identifier to type tracking.
type TVEnv = Map Var Type

-- Type checker environment:
-- - variable type tracking,
-- - alias type tracking,
-- - expected return type.
data TCEnv = CTCEnv {
    tvEnv :: TVEnv,
    taEnv :: TEnv,
    ret :: Maybe Type
    }

-- Casting rules:
-- - can cast between integers,
-- - can cast clean <-> const,
-- - cannot cast reference's underlying type,
-- - can take (and cast) cref of ref (but *not* ref of cref),
-- - cannot take ref of const variable (only cref),
-- - 
-- - can cast between aliases if the underlying type can be cast,
-- - tuple can be cast if all of its components do,
-- - array cannot be cast with modified element type,
-- - all casts are explicit,
-- - any cast which does not modify the type is allowed.