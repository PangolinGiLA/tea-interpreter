module ArithmeticUtils where

import Control.Monad
import Syntax.Abs (RValue(..), TInt(..), TPrim(..), TComp(..), TypeNoref(..), Type(..), TClean(..))
import VMTypes
import Utils (raiseError, raiseWarn, getType)

------------ Operator handling ------------

type ArgsCheck = Value -> Value -> VM ()

modArgsCheck :: ArgsCheck
modArgsCheck (Vint (i1, _)) (Vint (i2, _)) = do
    when (i2 == 0) (raiseError ModZero)

divArgsCheck :: ArgsCheck
divArgsCheck (Vint (i1, _)) (Vint (i2, _)) = do
    when (i2 == 0) (raiseError DivZero)

noCheck :: ArgsCheck
noCheck _ _ = return ()

binOp :: (Integer -> Integer -> Integer) -> Value -> Value -> VM Value
binOp op (Vint (i1, v)) (Vint (i2, _)) = do
    let res = op i1 i2
    fitInIntRange (res, v) Arithmetic

binOp op (Vchar c1) (Vchar c2) = do
    -- Char difference is by default I32.
    return $ Vint (op (fromChar c1) (fromChar c2), I32)

binOp op (Vchar c) (Vint (i, _)) = do
    res <- toChar $ op (fromChar c) i
    return $ Vchar res

unOp :: (Integer -> Integer) -> Value -> VM Value
unOp op (Vint (i, v)) = do
    let res = op i
    fitInIntRange (res, v) Arithmetic

------------ Char conversions ------------

fromChar :: Char -> Integer
fromChar c = fromIntegral $ fromEnum c

toChar :: Integer -> VM Char
toChar i = do
    when (i < minChar || i > maxChar) (raiseError $ CharOutOfBounds i)
    return $ toEnum $ fromIntegral i

minChar :: Integer
minChar = fromIntegral $ fromEnum (minBound::Char)
maxChar :: Integer
maxChar = fromIntegral $ fromEnum (maxBound::Char)

------------ Integer conversions ------------

-- Strip a no-ref type to TInt.
-- Note: the type may be aliased.
stripToInt :: TClean -> VM TInt
stripToInt (Tcomp (Tprim (Tint t))) = return t
stripToInt (Talias id) = do
    -- Get the aliased type as TComp.
    t <- getType id
    -- Strip again.
    stripToInt (Tcomp t)

cleanToVariety :: TClean -> VM IntVariety
cleanToVariety tclean = do
    t <- stripToInt tclean
    return (case t of
        Ti32 -> I32
        Ti64 -> I64
        Tu32 -> U32
        Tu64 -> U64)

fitInRange :: Integer -> (Integer, Integer) -> IntLossReason -> VM Integer
fitInRange n (minn, maxx) reason = do
    when (n < minn) (raiseWarn (IntLoss reason n minn))
    when (n > maxx) (raiseWarn (IntLoss reason n maxx))
    return $ max minn (min maxx n)

fitInIntRange :: (Integer, IntVariety) -> IntLossReason -> VM Value
fitInIntRange (i, v) reason = do
    let range =
            case v of
                I32 -> (-2147483648, 2147483647)
                I64 -> (-9223372036854775808, 9223372036854775807)
                U32 -> (0, 4294967295)
                U64 -> (0, 18446744073709551615)
    newI <- fitInRange i range reason
    return $ Vint (newI, v)

-- Integer conversions (with warnings)
convertInt :: (Integer, IntVariety) -> TClean -> VM Value
convertInt (i, v) t = do
    newVariety <- cleanToVariety t
    fitInIntRange (i, newVariety) Conversion

------------ Ordering ------------

leqThan :: Value -> Value -> Bool
leqThan (Vint (i1, _)) ((Vint (i2, _))) = i1 <= i2
leqThan (Vchar c1) (Vchar c2) = c1 <= c2

lessThan :: Value -> Value -> Bool
lessThan (Vint (i1, _)) ((Vint (i2, _))) = i1 < i2
lessThan (Vchar c1) (Vchar c2) = c1 < c2

------------ Increment/decrement ------------

-- Get the next value.
nextVal :: Value -> VM Value
nextVal (Vint (i, v)) = fitInIntRange (i + 1, v) Arithmetic
nextVal (Vchar c) = do
    newC <- toChar (fromChar c + 1)
    return $ Vchar newC

-- Get the previous value.
prevVal :: Value -> VM Value
prevVal (Vint (i, v)) = fitInIntRange (i - 1, v) Arithmetic
prevVal (Vchar c) = do
    newC <- toChar (fromChar c - 1)
    return $ Vchar newC

------------ Casting ------------

castTo :: Value -> Type -> VM Value
castTo v (TNoref (Tclean tclean)) = castToClean v tclean
castTo v (TNoref (Tconst tclean)) = castToClean v tclean
-- No ref casts mutate the underlying data.
castTo v _ = return v

castToClean :: Value -> TClean -> VM Value

-- Unpack aliases.
castToClean v (Talias id) = do
    t <- getType id
    castToClean v (Tcomp t)

-- Cast underlying tuple types.
castToClean (Vtup vals) (Tcomp (Ttup t1 tt)) = do
    castVals <- zipWithM castTo vals (t1:tt)
    return $ Vtup castVals

-- Cast integers.
castToClean (Vint iv) t = convertInt iv t
-- By default do nothing.
castToClean val _ = return val