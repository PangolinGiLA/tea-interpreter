module InterpretNode where
-- Interpreter of statements AND rvalues AND declarations
-- (together due to cyclic dependencies between them
-- when dealing with functions and state-modifying declarations).
import Control.Monad.Reader
import Control.Monad.Writer
import Syntax.Abs (Stmt(..), SBlock(..), CIdent(..), StringLiteral(..), SIf(..), RValue(..), TInt(..), Decl(..), VDecl(..), FDecl(..), Arg(..), LValue(..), IndexedArr(..), Interval(..), Type (..), TypeNoref (..))
import VMTypes
import Utils (
    getVElement, modifyTree, checkBounds,
    raiseError, returnValue,
    getLoc, getVal, movVal, hasVal, runWithEnv, addType,
    addLV,
    xor, iff, equal,
    getRetval, resizeArr, unpackVal)
import ArithmeticUtils (
    ArgsCheck,
    modArgsCheck, divArgsCheck, noCheck,
    convertInt, fitInIntRange,
    binOp, unOp,
    nextVal, prevVal,
    lessThan, leqThan, castTo)
import PrintUtils (toString)

------------ STATEMENTS INTERPRETER ------------

iS :: Stmt -> VM ()

iS (Sseq s1 s2) = do
    iS s1
    iS s2

iS Sskip = return ()

iS (Sassgn lv rv) = do
    val <- iRV rv
    setVal lv val

iS (Scall id rvs) = do
    -- Evaluate all args.
    args <- mapM iRV rvs

    (_, f) <- unpackVal id
    case f of
        Vfun fun -> do
            -- Ignore return value.
            _ <- fun (Vtup args)
            return ()
        _ -> raiseError PanicUnexpectedType

iS (Sprint rv) = do
    value <- iRV rv
    tell [Stdout (toString value)]

iS (Sresize id rv1 rv2) = do
    -- First, calculate the rvalues.
    val <- iRV rv1
    toFill <- iRV rv2

    (loc, arr) <- unpackVal id
    
    newArr <- case (arr, val, toFill) of
        (Varr a, Vint (n, _), _) -> do
            raw <- resizeArr a n toFill id
            return $ Varr raw
        (Vstr s, Vint (n, _), Vchar c) -> do
            raw <- resizeArr s n c id
            return $ Vstr raw
        _ -> raiseError PanicUnexpectedType

    movVal loc newArr

iS (Spush id rv) = do
    -- First, calculate the rvalue.
    val <- iRV rv

    (loc, arr) <- unpackVal id
    
    case (arr, val) of
        (Varr a, _) ->
            movVal loc (Varr (a ++ [val]))
        (Vstr s, Vchar c) ->
            movVal loc (Vstr (s ++ [c]))
        _ -> raiseError PanicUnexpectedType

iS (Spop id) = do
    let (CIdent (pos, name)) = id
    
    (loc, arr) <- unpackVal id

    case arr of
        Varr a -> do
            when (null a)
                (raiseError (PopEmpty pos name))
            movVal loc (Varr (init a))
        Vstr s -> do
            when (null s)
                (raiseError (PopEmpty pos name))
            movVal loc (Vstr (init s))
        _ -> raiseError PanicUnexpectedType

iS (Sassert rv (SLit str)) = do
    val <- iRV rv
    case val of
        Vbool True -> return ()
        _ -> raiseError (AssertionFailed str)

iS (Sreturn rv) = do
    val <- iRV rv
    returnValue val

iS Sretempty = returnValue Vvoid

iS (Sif i) = do
    case i of
        (SIfend rv b) -> do
            val <- iRV rv
            case val of
                Vbool True -> iS (Sblock b)
                Vbool False -> return ()
                _ -> raiseError PanicUnexpectedType
        (SIfelse rv b1 b2) -> do
            val <- iRV rv
            case val of
                Vbool True -> iS (Sblock b1)
                Vbool False -> iS (Sblock b2)
                _ -> raiseError PanicUnexpectedType
        (SIfelif rv b i') -> do
            val <- iRV rv
            case val of
                Vbool True -> iS (Sblock b)
                Vbool False -> iS (Sif i')
                _ -> raiseError PanicUnexpectedType

iS (Swhile rv b) = expandedWhile 
    -- This is a fixed-point equation.
    where expandedWhile = do
            val <- iRV rv
            case val of
                Vbool True -> do
                    iS (Sblock b)
                    expandedWhile
                Vbool False -> return ()
                _ -> raiseError PanicUnexpectedType

iS (Sfor id int b) = do
    -- Interval ranges are calculated once.
    lower <- intervalLower int
    upper <- intervalUpper int
    -- Add the iterator variable.
    newEnv <- addLVVal (LVId id) lower
    loc <- runWithEnv newEnv $ getLoc id
    -- Run with the new environment.
    runWithEnv newEnv $ executeFor (Sblock b) loc upper

iS (Sblock b) =
    case b of
        Sblocks s -> do
            iS s
        Sblockd d -> do
            iD d
            return ()
        Sblockds d s -> do
            newEnv <- iD d
            runWithEnv newEnv (iS s)

------------ DECLARATIONS INTERPRETER ------------

iD :: Decl -> VM Env

iD (Dseq d1 d2) = do
    newEnv <- iD d1
    runWithEnv newEnv (iD d2)

iD (Vdecl d) = do
    case d of
        VDNoinit lv t -> addLV lv
        VDType lv t rv -> do
            val <- iRV rv
            addLVVal lv val
        VDNotype lv rv -> do
            val <- iRV rv
            addLVVal lv val

iD (Fdecl (FDType id args _ b)) = do
    let lv = LVId id
    -- Add the function's name to the current environment.
    recursionEnv <- addLV lv
    -- Create the function as a value.
    f <- runWithEnv recursionEnv (createFun args b)
    -- Assign it the created value.
    runWithEnv recursionEnv $ setVal lv f
    -- Return the new environment.
    return recursionEnv

iD (DAlias tid t) = addType tid t

------------ RVAlUES INTERPRETER ------------

iRV :: RValue -> VM Value

------------ Boolean expressions ------------

iRV (BOr rv1 rv2) = iRVBoolOp (||) rv1 rv2
iRV (BAnd rv1 rv2) = iRVBoolOp (&&) rv1 rv2
iRV (BXor rv1 rv2) = iRVBoolOp xor rv1 rv2
iRV (BBeq rv1 rv2) = iRVBoolOp iff rv1 rv2

iRV (BNot rv) = do
    val <- iRV rv
    case val of
        Vbool b -> return $ Vbool (not b)
        _ -> raiseError PanicUnexpectedType

iRV (BAeq rv1 rv2) = do
    val1 <- iRV rv1
    val2 <- iRV rv2
    return $ Vbool (equal val1 val2)

iRV (BAle rv1 rv2) = do
    val1 <- iRV rv1
    val2 <- iRV rv2
    return $ Vbool (lessThan val1 val2)

iRV (BAleq rv1 rv2) = do
    val1 <- iRV rv1
    val2 <- iRV rv2
    return $ Vbool (leqThan val1 val2)

------------ Arithmetics ------------

iRV (AMod rv1 rv2) = iRVArBinOp mod modArgsCheck rv1 rv2
iRV (APlus rv1 rv2) = iRVArBinOp (+) noCheck rv1 rv2
iRV (AMinus rv1 rv2) = iRVArBinOp (-) noCheck rv1 rv2
iRV (AMul rv1 rv2) = iRVArBinOp (*) noCheck rv1 rv2
iRV (ADiv rv1 rv2) = iRVArBinOp div divArgsCheck rv1 rv2

iRV (ANeg rv) = iRVArUnOp negate rv

------------ Miscellaneous ------------

iRV (RVCast t rv) = do
    val <- iRV rv
    castTo val t

-- Alias unpacking makes no real casts.
iRV (RVAcast _ rv) = iRV rv

iRV (RVTup rv rvList) = do
    val <- iRV rv
    vals <- mapM iRV rvList
    return $ Vtup (val : vals)

iRV (RVArr rvList) = do
    vals <- mapM iRV rvList
    return $ Varr vals

iRV (RVArrEmpty _) = do
    return $ Varr []

iRV (RVLambda args _ b) = createFun args b

------------ Literals ------------

iRV RVTrue = return $ Vbool True
iRV RVFalse = return $ Vbool False

-- By default, all integers are 64-bit, signed.
iRV (RVNum n) = do
    fitInIntRange (n, I64) Literal

iRV (RVChar c) = return $ Vchar c

iRV (RVString (SLit s)) = return $ Vstr s

------------ Identifiers and references ------------

-- Note: the type of every identifier used in an rvalue
-- decays (ref -> noref, noref -> noref).
-- Both type checking and semantics work accordingly.
-- That is, in the below snippet:

-- let x: u32 = 0;
-- let y = ref x;
-- let z = y;

-- Variable z is of type u32, and *not* ref u32.
-- If we want it to be ref u32, we need to write:

-- let z = ref y;

-- However, only identifiers' types decay! That is,
-- we *cannot* write: (2 + ref x), because type of ref x
-- is a reference (and array elements do not decay either!).

iRV (RVId id) = do
    loc <- getLoc id
    v <- getVal loc
    case v of
        Ref loc2 -> getVal loc2 -- Ref decay.
        _ -> return v

iRV (RVRcast id) = do
    loc <- getLoc id
    v <- getVal loc -- <- A variable must be initialized to take a ref to it!
    case v of
        Ref loc2 -> return v -- Single ref decay (we end up with one-level ref).
        _ -> return $ Ref loc

iRV (RVRccast id) = iRV (RVRcast id)

------------ Function calls ------------

-- Function call. Note that the function's arguments
-- are *always* packed in a tuple upon a call
-- and unpacked in each function's definition.
iRV (RVCall id rvs) = do
    -- Calculate all arguments.
    args <- mapM iRV rvs
    
    (_, f) <- unpackVal id
    
    case f of
        Vfun fun -> do
            -- Call the function
            fun $ Vtup args
        _ -> raiseError PanicUnexpectedType

-- Size is signed, 64-bit.
-- Size support for both arrays and strings.
iRV (RVSize id) = do
    (_, val) <- unpackVal id
    
    case val of
        Varr a -> return $ Vint (fromIntegral $ length a, I64)
        Vstr s -> return $ Vint (fromIntegral $ length s, I64)
        _ -> raiseError PanicUnexpectedType

-- Checks for array bounds.
-- Note: every reference to array/string is decayed
-- when indexed (for usability purposes).
-- However, beware! If the accessed element is not
-- indexed anymore, it is *not* decayed.
-- That is, you can have:

-- let x = 1;
-- let t = [ref x, ref x];
-- let x2 = t[0];
-- x2 = 2;
-- assert(x == 2, "equal");

-- But you cannot write:

-- let x = 1;
-- let t = [ref x, ref x];
-- assert(t[0] == 1, "equal");
-- [Error] -----^---- types `ref i64` and `i64` don't match

iRV (RVIndex (IAStart id rv)) = do
    -- First, perform ref decay.
    arr <- iRV (RVId id)
    -- Then access the element.
    getElementRV arr rv

iRV (RVIndex (IACont ia rv)) = do
    -- First access the ia indexed array element
    -- (important due to mutating expressions!).
    arr <- iRV (RVIndex ia)
    -- Type-checker guarantees arr is an (ref to) array/string.
    -- Perform indexed ref decay.
    arr <- case arr of
        Ref loc -> getVal loc
        _ -> return arr
    -- Access the element.
    getElementRV arr rv

------------ Helper functions with cyclic dependencies ------------

------ Arithmetics ------

iRVBoolOp :: (Bool -> Bool -> Bool) -> RValue -> RValue -> VM Value
iRVBoolOp op rv1 rv2 = do
    val1 <- iRV rv1
    val2 <- iRV rv2
    case (val1, val2) of
        (Vbool b1, Vbool b2) -> return $ Vbool (op b1 b2)
        _ -> raiseError PanicUnexpectedType

iRVArBinOp :: (Integer -> Integer -> Integer) -> ArgsCheck -> RValue -> RValue -> VM Value
iRVArBinOp op argsCheck rv1 rv2 = do
    v1 <- iRV rv1
    v2 <- iRV rv2
    argsCheck v1 v2
    binOp op v1 v2

iRVArUnOp :: (Integer -> Integer) -> RValue -> VM Value
iRVArUnOp op rv = do
    val <- iRV rv
    unOp op val

------ RValues utils ------

-- Calculate index and access array/string element.
getElementRV :: Value -> RValue -> VM Value
getElementRV arr rv = do
    val <- iRV rv
    idx <- checkBounds arr val
    return $ getVElement arr idx

------ Env/Store manipulation ------

-- Store assignment with tuple unpacking: "lv = val".
-- Checks for use of undeclared lvalues.
setVal :: LValue -> Value -> VM ()
setVal (LVId id) val = do
    loc <- getLoc id
    initialized <- hasVal loc
    -- Note: type-checker guarantees that uninitialized
    -- references will *not* be assigned no-ref values.
    if initialized then do
            oldVal <- getVal loc
            case (oldVal, val) of
                (Ref _, Ref _) -> movVal loc val
                (Ref l, _) -> movVal l val
                (_, _) -> movVal loc val
    else movVal loc val

setVal (LVTup lv lvList) (Vtup els) =
    case lvList of
        [] -> let [el] = els in
            setVal lv el
        _ -> let (el:t) = els in do
            setVal lv el
            zipWithM_ setVal lvList t

setVal (ALVArr ia) val = do
    -- Get the path from root to the modified node.
    -- Note: the root needs not be the node of the identifier,
    -- e.g. when at some depth there are references to arrays.
    (path, loc0) <- accessPath ia
    case path of
        (_, _, lastVal):t -> do
            -- Modify the array contents accordingly.
            case (lastVal, val) of
                (Ref _, Ref _) -> movVal loc0 (modifyTree path val)
                (Ref l, _) -> movVal l val
                (_, _) -> movVal loc0 (modifyTree path val)

        _ -> raiseError PanicUnexpectedType

-- Note: the "path" always consists of (array/string, int),
-- there are no references there. In fact, upon a reference,
-- the path and the base location are reset.
accessPath :: IndexedArr -> VM ([(Value, Int, Value)], Loc)
accessPath (IAStart id rv) = do
    loc <- getLoc id
    arr <- getVal loc
    idxVal <- iRV rv
    -- Get the real array and its location (arr might be a reference).
    (arr, loc) <- case arr of
        Ref loc2 -> do
            arr2 <- getVal loc2
            return (arr2, loc2)
        _ -> return (arr, loc)
    -- Check the array bounds.
    idx <- checkBounds arr idxVal
    -- Return the path and last value.
    return ([(arr, idx, getVElement arr idx)], loc)

accessPath (IACont ia rv) = do
    -- First access previous arrays
    -- (important due to mutating expressions!).
    (path, loc0) <- accessPath ia
    -- Then evaluate the next index.
    case path of
        (_, _, lastVal):t -> do
            idxVal <- iRV rv
            (arr, path, loc) <- case lastVal of
                Ref loc2 -> do
                    arr <- getVal loc2
                    -- A reference resets the path and base location.
                    return (arr, [], loc2)
                _ -> return (lastVal, path, loc0)
            -- Check the array bounds.
            idx <- checkBounds arr idxVal
            -- Update the path.
            return ((arr, idx, getVElement arr idx) : path, loc)

        _ -> raiseError PanicUnexpectedType

-- "let lv = val": declare lv, assign val
-- Note that non-declarative lvalues are not supported
-- as they are filtered out by the type-checker.
addLVVal :: LValue -> Value -> VM Env
addLVVal lv val = do
    newEnv <- addLV lv
    runWithEnv newEnv (setVal lv val)
    return newEnv

-- Increment the value under given location.
incVal :: Loc -> VM ()
incVal loc = do
    val <- getVal loc
    newVal <- nextVal val
    movVal loc newVal

------ Functions ------

-- Arguments are declared sequentially, that is,
-- latter ones overshadow previous ones.
declareArgs :: [(Arg, Value)] -> VM Env
declareArgs [] = ask
declareArgs ((FArg id _, v):t) = do
    env <- addLVVal (LVId id) v
    runWithEnv env (declareArgs t)

createFun :: [Arg] -> SBlock -> VM Value
createFun argNames b = do
    -- Retrieve the current environment.
    denv <- ask
    -- Define function body.
    let f v = case v of
            Vtup args -> do
                -- Declare and assign args in the declaration's env.
                env <- runWithEnv denv (declareArgs $ zip argNames args)
                -- Run the body and return the ret value.
                getRetval (runWithEnv env $ iS (Sblock b))
            _ -> raiseError PanicUnexpectedType

    return $ Vfun f

------ For loop ------

executeFor :: Stmt -> Loc -> Value -> VM ()
executeFor b loc upper = expandedExecuteFor
    where expandedExecuteFor = do
            i <- getVal loc
            when (leqThan i upper) (do
                iS b
                incVal loc
                expandedExecuteFor)

intervalUpper :: Interval -> VM Value
intervalUpper (IntervalII _ rv) = iRV rv
intervalUpper (IntervalIE _ rv) = do
    val <- iRV rv
    prevVal val
intervalUpper (IntervalEI x rv) = intervalUpper (IntervalII x rv)
intervalUpper (IntervalEE x rv) = intervalUpper (IntervalIE x rv)

intervalLower :: Interval -> VM Value
intervalLower (IntervalII rv _) = iRV rv
intervalLower (IntervalEI rv _) = do
    val <- iRV rv
    nextVal val
intervalLower (IntervalIE rv x) = intervalLower (IntervalII rv x)
intervalLower (IntervalEE rv x) = intervalLower (IntervalEI rv x)