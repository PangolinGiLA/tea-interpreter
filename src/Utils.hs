module Utils where

import Data.Bits ((.&.), shiftL)
import Data.Map
import qualified GHC.Integer (leInteger)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Syntax.Abs (CIdent(..), LValue(..), Arg(..), SBlock(..), TClean(..), TComp(..))
import VMTypes

------------ General utils ------------

getVElement :: Value -> Int -> Value
getVElement (Varr arr) i = arr !! i
getVElement (Vstr s) i = Vchar (s !! i)

-- Return an array with a modified i-th element.
setElement :: [a] -> Int -> a -> [a]
setElement arr idx v =
    let (beg, _:end) = Prelude.splitAt idx arr in
        beg ++ v : end

setVElement :: Value -> Int -> Value -> Value
setVElement (Varr arr) idx val =
    Varr (setElement arr idx val)
setVElement (Vstr str) idx (Vchar c) =
    Vstr (setElement str idx c)

-- Modify the tree-like array structure specified by
-- the first argument (a path from the root).
modifyTree :: [(Value, Int, Value)] -> Value -> Value
modifyTree [(arr, i, _)] val = setVElement arr i val
modifyTree ((arr, i, _):t) val = modifyTree t $ setVElement arr i val

checkArrBounds :: [a] -> Value -> VM Int
checkArrBounds arr (Vint (i, _)) = do
    let len = fromIntegral (length arr)
    when (i >= len || i < 0)
        (raiseError (ArrOutOfBounds i len))
    return $ fromIntegral i

-- Check if the index (#2) is inside the bounds of an array-like type (#1)
-- and return the index as Int.
checkBounds :: Value -> Value -> VM Int
checkBounds (Varr a) = checkArrBounds a
checkBounds (Vstr s) = checkArrBounds s

------------ Map utils ------------

mapHas :: (Ord k) => Map k v -> k -> Bool
mapHas map arg = member arg map

mapGet :: (Ord k) => Map k v -> k -> v
mapGet map arg = map ! arg

mapSet :: (Ord k) => Map k v -> k -> v -> Map k v
mapSet map arg val = insert arg val map

------------ Warnings, Errors and return values ------------

raiseWarn :: Warning -> VM ()
raiseWarn w = do
    tell [Stderr (Warn w)]

raiseError :: Error -> VM a
raiseError e = do
    throwError (Left e)

returnValue :: RetVal -> VM ()
returnValue ret = do
    throwError (Right ret)

------------ Store manipulation ------------

-- Get the value behind an allocated location.
-- Checks if the location was initialized.
getVal :: Loc -> VM Value
getVal loc = do
    sto <- get
    let stoMap = currMap sto
    unless (mapHas stoMap loc)
        (raiseError (UseUninit loc))
    return $ mapGet stoMap loc

-- Get the underlying (loc, value) of id (unpack references).
unpackVal :: CIdent -> VM (Loc, Value)
unpackVal id = do
    -- Level 0.
    loc0 <- getLoc id
    v0 <- getVal loc0
    case v0 of
        Ref loc1 -> do
            -- Level 1.
            v1 <- getVal loc1
            return (loc1, v1)
        _ -> return (loc0, v0)

hasVal :: Loc -> VM Bool
hasVal loc = do
    sto <- get
    let res = mapHas (currMap sto) loc 
    return res

-- Put the value into a valid location: "mov [loc], val".
movVal :: Loc -> Value -> VM ()
movVal loc val = do
    sto <- get
    let oldLoc = nextLoc sto
    let newMap = mapSet (currMap sto) loc val
    let newStore = CStore newMap oldLoc
    put newStore

------------ Env manipulation ------------

newLoc :: VM Loc
newLoc = do
    (CStore map loc) <- get
    put (CStore map (loc + 1))
    return (loc + 1)

-- Get the variable environment.
getVEnv :: VM VEnv
getVEnv = asks varEnv

-- Make Env using the current TEnv and supplied VEnv.
makeEnv :: VEnv -> VM Env
makeEnv venv = do
    tenv <- asks typeEnv
    return $ CEnv venv tenv

getType :: CIdent -> VM TComp
getType (CIdent (pos, name)) = do
    tenv <- asks typeEnv
    return $ mapGet tenv name

addType :: CIdent -> TClean -> VM Env
addType (CIdent (pos, name)) t = do
    -- Note: type-checker guarantees that this name
    -- aliases no other type in the current TEnv map
    -- (it might alias the same one if we use the declaration
    -- in a loop).
    tenv <- asks typeEnv
    -- Check if t itself is an alias.
    tReal <- case t of
        Talias id -> getType id
        Tcomp tt -> return tt
    -- Update the TEnv map.
    let newTEnv = mapSet tenv name tReal
    -- Return the modified Env.
    venv <- getVEnv
    return $ CEnv venv newTEnv

-- Get the location of the identifier.
-- Handles undeclared use errors.
getLoc :: CIdent -> VM Loc
getLoc (CIdent (pos, name)) = do
    venv <- getVEnv
    unless (mapHas venv name)
        (raiseError (Undeclared pos name))
    return $ mapGet venv name

-- "let lv": declare lv
-- Note that non-declarative lvalues are not supported
-- as they're filtered out by the type-checker.
addLV :: LValue -> VM Env
addLV (LVId (CIdent (pos, name))) = do
    venv <- getVEnv
    -- Apply mapSet to the result of newLoc.
    newVEnv <- mapSet venv name <$> newLoc
    makeEnv newVEnv

addLV (LVTup lv lvList) = do
    env <- addLV lv
    runWithEnv env (case lvList of
        [] -> ask
        [lv2] -> addLV lv2
        (lv2:t) -> do
            env <- addLV lv2
            let (lv3:tt) = t
            runWithEnv env (addLV (LVTup lv3 tt)))

runWithEnv :: Env -> VM a -> VM a
runWithEnv env vm = do
    local (const env) vm

------------ Boolean functions ------------

xor :: Bool -> Bool -> Bool
xor b1 b2 = (b1 || b2) && not (b1 && b2)

iff :: Bool -> Bool -> Bool
iff b1 b2 = (b1 && b2) || (not b1 && not b2)

------------ Operations on values ------------

equal :: Value -> Value -> Bool
equal v1 v2 = case (v1, v2) of
    (Vint (i1, _), Vint (i2, _)) -> i1 == i2
    (Vbool b1, Vbool b2) -> b1 == b2
    (Vchar c1, Vchar c2) -> c1 == c2
    (Vstr s1, Vstr s2) -> s1 == s2
    (Varr a, Varr b) -> all (uncurry equal) (zip a b)
    (Vtup a, Vtup b) -> all (uncurry equal) (zip a b)
    (Ref l1, Ref l2) -> l1 == l2

------------ Functions ------------

-- Run a statement and catch a return value.
getRetval :: VM () -> VM Value
getRetval exec = do
    -- We need VM Value type for catchError
    -- signature.
    -- By default a function returns void,
    -- violations of return type are checked
    -- by the type-checker.
    let dummyRet = do
            exec
            return Vvoid
    catchError dummyRet retvalIntercept

-- Different control flow interception behaviour
-- after running a function body.
retvalIntercept :: DiffCFlow -> VM Value
-- Upon error, reraise it.
retvalIntercept (Left err) = raiseError err
-- Upon retval, return it.
retvalIntercept (Right ret) = return ret

------------ Indexed values utils ------------

resizeArr :: [a] -> Integer -> a -> CIdent -> VM [a]
resizeArr arr n toFill (CIdent (pos, name)) = do
    when (n < 0)
        (raiseError (NegativeSize pos name))
    let len = fromIntegral (length arr)
    if n <= len
        then return (Prelude.take (fromIntegral n) arr)
    else do
        let newVals = replicate (fromIntegral (n - len)) toFill
        return (arr ++ newVals)