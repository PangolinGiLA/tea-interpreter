module TypeCheckNode where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Syntax.Abs (Type(..), TypeNoref(..), TInt(..), Stmt(..), SBlock(..), CIdent(..), StringLiteral(..), SIf(..), RValue(..), TInt(..), Decl(..), VDecl(..), FDecl(..), Arg(..), LValue(..), IndexedArr(..), Interval(..), TypeNoref, TClean (..), TComp (..), TPrim (..), TFuns (..), TypeRef (..))

import TCTypes
import TypeCheckUtils
import Utils (mapHas, mapGet, mapSet)

------------ STATEMENTS TYPE CHECK ------------

-- Function returns if the instruction always finishes with a return.
tcS :: Stmt -> TC Bool

tcS (Sseq s1 s2) = do
    v1 <- tcS s1
    when v1 (
        signalWarn DeadCode)
    v2 <- tcS s2

    return (v1 || v2)

tcS Sskip = return False

tcS (Sassgn lv rv) = do
    trv <- tcRV rv
    tlv <- getLVType lv
    -- Match types.
    checkAssgnTypes tlv trv
    -- Check for mutability of all lvalues.
    checkLVMut lv
    return False

tcS (Scall id rvs) = do
    trvs <- mapM tcRV rvs
    let trv = argsType trvs

    -- Get function and arguments types.
    tid <- getLVType (LVId id)
    (targs, tret) <- assumeFun tid
    
    checkTypes targs trv

    -- Signal warning if unused return value.
    case tret of
        TNoref (Tclean (Tcomp (Tprim Tvoid))) -> return ()
        _ -> do
            let (CIdent (pos, name)) = id
            signalWarn $ UnusedReturn pos name

    return False

-- Can print any type.
tcS (Sprint rv) = do
    _ <- tcRV rv
    return False

tcS (Sresize id rvSize rvFill) = do
    trvSize <- tcRV rvSize
    trvFill <- tcRV rvFill
    -- Get array and element types.
    tid <- getLVType (LVId id)
    tel <- assumeIndexed tid
    -- Check size type.
    checkSizeType trvSize
    -- Check fill type.
    checkTypes tel trvFill
    -- Check for mutability
    checkMut tid
    return False

tcS (Spush id rv) = do
    trv <- tcRV rv
    -- Get array type.
    tid <- getLVType (LVId id)
    -- Get element type.
    tel <- assumeIndexed tid
    -- Match with rvalue type.
    checkTypes tel trv
    -- Check for mutability.
    checkMut tid
    return False

tcS (Spop id) = do
    tid <- getLVType (LVId id)
    _ <- assumeIndexed tid
    checkMut tid
    return False

tcS (Sassert rv _) = do
    trv <- tcRV rv
    checkTypes boolType trv
    return False

tcS (Sreturn rv) = do
    trv <- tcRV rv
    expect <- asks ret
    case expect of
        Just t -> checkTypes t trv
        Nothing -> throwError UncaughtReturn
    return True

tcS Sretempty = do
    expect <- asks ret
    case expect of
        Just t -> checkTypes t voidType
        Nothing -> throwError UncaughtReturn
    return True

tcS (Sif i) = do
    case i of
        (SIfend rv b) -> do
            trv <- tcRV rv
            checkTypes boolType trv
            tcS (Sblock b)
            -- The condition may be false, thus we cannot guarantee a return.
            return False
        (SIfelse rv b1 b2) -> do
            trv <- tcRV rv
            checkTypes boolType trv
            v1 <- tcS (Sblock b1)
            v2 <- tcS (Sblock b2)
            return (v1 && v2)
        (SIfelif rv b i') -> do
            trv <- tcRV rv
            checkTypes boolType trv
            v1 <- tcS (Sblock b)
            v2 <- tcS (Sif i')
            return (v1 && v2)

tcS (Swhile rv b) = do
    trv <- tcRV rv
    checkTypes boolType trv
    tcS (Sblock b)
    return False

tcS (Sfor id int b) = do
    ti <- tcRVIntervalType int
    newEnv <- newTCEnv id ti
    runWithTCEnv newEnv $ tcS (Sblock b)
    return False
    
tcS (Sblock b) = 
    case b of
        Sblocks s -> do
            tcS s
        Sblockd d -> do
            tcD d
            return False
        Sblockds d s -> do
            newEnv <- tcD d
            runWithTCEnv newEnv (tcS s)

------------ DECLARATIONS TYPE CHECK ------------

tcD :: Decl -> TC TCEnv

tcD (Dseq d1 d2) = do
    newEnv <- tcD d1
    runWithTCEnv newEnv (tcD d2)

tcD (Vdecl d) = do
    case d of    
        VDNoinit lv t -> do
            checkTypeExists t
            checkNoref t
            setLVType lv t
        VDNotype lv rv -> do
            trv <- tcRV rv
            setLVType lv trv
        VDType lv t rv -> do
            trv <- tcRV rv
            -- The specified type must match the rvalue type exactly.
            -- It is only a readability feature (semantically redundant).
            checkTypeExists t
            checkTypes t trv
            setLVType lv trv

tcD (Fdecl (FDType id args tret b)) = do
    -- Both argument and return types must exist.
    let targs = fArgsType args
    checkTypeExists targs
    checkTypeExists tret
    -- Important! Declared functions are const, so they cannot
    -- have their body reassigned later.
    let ftype = TNoref (Tconst (Tcomp (Tfun (TFun targs tret))))
    -- Add function name to its environment.
    fenvOut <- newTCEnv id ftype
    -- Add arguments to the environment (arguments shadow the function name).
    fenvIn <- runWithTCEnv fenvOut (declareArgsT args)
    -- Add return type to the environment.
    let fullEnv = makeTCEnvF fenvIn tret
    -- Type check the function block.
    returned <- runWithTCEnv fullEnv (tcS (Sblock b))
    unless (returned || equalT voidType tret) (
        throwError NoReturn)
    
    -- Add function id to the current environment.
    return fenvOut

tcD (DAlias (CIdent (pos, name)) t) = do
    checkTypeCleanExists t

    aEnv <- asks taEnv
    let aliasExists = mapHas aEnv name
    -- Aliases cannot be shadowed.
    when aliasExists
        (throwError $ AliasShadowing pos name)

    let tReal = case t of
            -- The alias map is flat.
            (Talias (CIdent (_, id))) -> mapGet aEnv id
            (Tcomp tt) -> tt
    
    makeTCEnvA $ mapSet aEnv name tReal

------------ RVALUES TYPE CHECK ------------

tcRV :: RValue -> TC Type

tcRV (BOr rv1 rv2) = tcRVBoolOp rv1 rv2
tcRV (BAnd rv1 rv2) = tcRVBoolOp rv1 rv2
tcRV (BXor rv1 rv2) = tcRVBoolOp rv1 rv2
tcRV (BBeq rv1 rv2) = tcRVBoolOp rv1 rv2

tcRV (BNot rv) = do
    trv <- tcRV rv
    checkTypes boolType trv
    return boolType

tcRV (BAeq rv1 rv2) = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    checkTypes trv1 trv2
    return boolType

tcRV (BAle rv1 rv2) = tcRVIntOrChar rv1 rv2
tcRV (BAleq rv1 rv2) = tcRVIntOrChar rv1 rv2

tcRV (AMod rv1 rv2) = tcRVIntOp rv1 rv2
tcRV (AMul rv1 rv2) = tcRVIntOp rv1 rv2
tcRV (ADiv rv1 rv2) = tcRVIntOp rv1 rv2
tcRV (APlus rv1 rv2) = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    case (trv1, trv2) of 
        (TNoref (Tclean (Tcomp (Tprim Tchar))), TNoref (Tclean (Tcomp (Tprim (Tint _))))) -> return charType
        (TNoref (Tclean (Tcomp (Tprim (Tint _)))), TNoref (Tclean (Tcomp (Tprim (Tint _))))) -> do
            checkTypes trv1 trv2
            return trv1
        _ -> throwError $ PlusMismatch trv1 trv2
            
tcRV (AMinus rv1 rv2) = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    case (trv1, trv2) of 
        (TNoref (Tclean (Tcomp (Tprim Tchar))), TNoref (Tclean (Tcomp (Tprim (Tint _))))) -> return charType
        (TNoref (Tclean (Tcomp (Tprim (Tint _)))), TNoref (Tclean (Tcomp (Tprim (Tint _))))) -> do
            checkTypes trv1 trv2
            return trv1
        (TNoref (Tclean (Tcomp (Tprim Tchar))), TNoref (Tclean (Tcomp (Tprim Tchar)))) -> return defaultIntType
        _ -> throwError $ MinusMismatch trv1 trv2
 
tcRV (ANeg rv) = do
    trv <- tcRV rv
    case trv of 
        TNoref (Tclean (Tcomp (Tprim (Tint Ti32)))) -> return trv
        TNoref (Tclean (Tcomp (Tprim (Tint Ti64)))) -> return trv
        _ -> throwError $ ExpectedSigned trv

tcRV (RVCast t rv) = do
    trv <- tcRV rv
    checkCast t trv
    -- The checkCast makes sure that `t` is well formed.
    return t

tcRV (RVAcast id rv) = do
    trv <- tcRV rv
    -- Check if alias exists.
    tal <- getAliasType id
    -- Noref, clean alias must match the rvalue type exactly.
    checkTypes (aliasType id) trv
    return $ cleanType tal

tcRV (RVTup rv rvList) = do
    case rvList of
        [] -> throwError InvalidTupleSize
        _ -> do
            trv <- tcRV rv
            trvs <- mapM tcRV rvList
            return $ tupleType trv trvs

tcRV (RVArr rvList) = do
    if null rvList then
        throwError EmptyArray
    else do
        t <- tcRV (head rvList)
        types <- mapM tcRV rvList
        if all (equalT t) types then
            return $ arrType t
        else
            throwError DifferentArrayTypes

tcRV (RVArrEmpty t) = do
    checkTypeExists t
    return $ arrType t

tcRV (RVLambda args tret b) = do
    let targs = fArgsType args
    checkTypeExists targs
    checkTypeExists tret

    fenv <- declareArgsT args
    let fullEnv = makeTCEnvF fenv tret
    returned <- runWithTCEnv fullEnv (tcS (Sblock b))
    unless (returned || equalT voidType tret) (
        throwError NoReturn)

    -- Lambdas are mutable by default.
    return $ compType (Tfun (TFun targs tret))

tcRV RVTrue = return boolType
tcRV RVFalse = return boolType

tcRV (RVNum n) = return defaultIntType 

tcRV (RVChar c) = return charType

tcRV (RVString (SLit s)) = return stringType

tcRV (RVId id) = do
    tid <- getLVType (LVId id)
    -- Perform ref decay, keep mutability.
    case tid of
        TNoref t -> return tid
        TRef (Tref t) -> return $ TNoref (Tclean t)
        TRef (Tcref t) -> return $ TNoref (Tconst t)

tcRV (RVRcast id) = do
    tid <- getLVType (LVId id)
    -- Check for mutability.
    case tid of
        TNoref (Tclean t) -> return $ TRef (Tref t)
        TNoref (Tconst t) -> throwError $ ConstViolation tid
        TRef (Tref t) -> return tid
        TRef (Tcref t) -> throwError $ ConstViolation tid

tcRV (RVRccast id) = do
    tid <- getLVType (LVId id)
    -- No requirements on tid mutability.
    case tid of
        TNoref (Tclean t) -> return $ TRef (Tcref t)
        TNoref (Tconst t) -> return $ TRef (Tcref t)
        TRef (Tref t) -> return $ TRef (Tcref t)
        _ -> return tid

tcRV (RVCall id rvs) = do
    -- Check arguments.
    trvs <- mapM tcRV rvs
    let trv = argsType trvs

    -- Get the function type.
    tid <- getLVType (LVId id)
    (targs, tret) <- assumeFun tid

    -- Match argument types
    checkTypes targs trv

    return tret

tcRV (RVSize id) = do
    tid <- getLVType (LVId id)
    _ <- assumeIndexed tid
    return usizeType

tcRV (RVIndex ia) = assumeIA ia

------------ UTILS ------------

-- Get lvalue type and check for any static errors.
getLVType :: LValue -> TC Type
getLVType (LVId cid) = getVarType cid 

getLVType (LVTup lv lvList) =
    case lvList of
        [] -> throwError InvalidTupleSize
        _ -> do
            t1 <- getLVType lv
            ts <- mapM getLVType lvList
            return $ compType (Ttup t1 ts)

getLVType (ALVArr ia) = assumeIA ia

setLVType :: LValue -> Type -> TC TCEnv
setLVType (LVId cid) t = newTCEnv cid t

setLVType (LVTup lv lvList) t =
    case t of
        (TRef _) -> throwError $ UnpackedRefTuple t
        _ -> setLVTupType (LVTup lv lvList) (stripClean t)

setLVType (ALVArr _) _ = throwError ArrayLvalue

setLVTupType :: LValue -> TClean -> TC TCEnv
setLVTupType (LVTup lv lvList) t =
    case t of
        (Tcomp (Ttup t1 tt)) ->
            if null tt then
                throwError InvalidTupleSize
            else if length tt /= length lvList then
                throwError TupleUnpackingMismatch 
            else
                processLVTypeList $ zip (lv:lvList) (t1:tt)

        _ -> throwError TupleUnpackingMismatch

processLVTypeList :: [(LValue, Type)] -> TC TCEnv
processLVTypeList arr =
    case arr of
        [] -> ask
        ((lv, t):tl) -> do
            env <- setLVType lv t
            runWithTCEnv env (processLVTypeList tl)

-- Check if the lvalue is mutable.
checkLVMut :: LValue -> TC ()
checkLVMut (LVId id) = do
    t <- getLVType (LVId id)
    checkMut t

checkLVMut (LVTup lv lvList) =
    case lvList of
        [] -> throwError InvalidTupleSize
        _ -> mapM_ checkLVMut (lv:lvList)

checkLVMut (ALVArr ia) = checkIAMut ia

-- Get the indexed array's element type and check for static errors.
-- The resolution order:
--      tab[rv1][rv2][rv3]
--                    ^ 1st
--               ^ 2nd
--          ^ 3rd
--      ^ 4th
--             ^ 5th
--                  ^ 6th
--                       ^ 7th
-- (first, rvalues: right to left; then tab id;
-- rvalue types and then indexed tab: left to right).
assumeIA :: IndexedArr -> TC Type
assumeIA (IAStart id rv) = do
    -- Check the rvalue.
    trv <- tcRV rv
    -- Get and check the array type.
    t0 <- getLVType (LVId id)
    tel <- assumeIndexed t0
    -- Check the rvalue type.
    checkSizeType trv
    -- Return the element type.
    return tel

assumeIA (IACont ia rv) = do
    -- Check the rvalue.
    trv <- tcRV rv
    -- Get and check the ia type.
    tprev <- assumeIA ia
    tel <- assumeIndexed tprev
    -- Check the rvalue type.
    checkSizeType trv
    -- Return the element type.
    return tel

-- Check whether the indexed array can be modified
-- (aka if there are *no* const/cref modifiers from root).
-- First checks for correct indexing, then constness.
checkIAMut :: IndexedArr -> TC ()
checkIAMut ia = do
    _ <- assumeIA ia
    _ <- assumeIAMut ia
    return ()

-- Internal IA mutability checker. Does not check for rvalue correctness.
assumeIAMut :: IndexedArr -> TC Type
assumeIAMut (IAStart id _) = do
    -- Get and check the array type.
    t0 <- getLVType (LVId id)
    tel <- assumeIndexed t0
    -- Check for mutability
    checkMut t0
    checkMut tel
    -- Return the element type.
    return tel

assumeIAMut (IACont ia _) = do
    tprev <- assumeIAMut ia
    tel <- assumeIndexed tprev
    checkMut tel
    return tel

-- Arythmetics checker

tcRVBoolOp :: RValue -> RValue -> TC Type
tcRVBoolOp rv1 rv2 = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    checkTypes boolType trv1
    checkTypes boolType trv2
    return boolType

-- Check if rvalues have equal, clean int/char type and return bool.
tcRVIntOrChar :: RValue -> RValue -> TC Type
tcRVIntOrChar rv1 rv2 = do
    _ <- tcRVIntOrCharType rv1 rv2
    return boolType

tcRVIntOp :: RValue -> RValue -> TC Type
tcRVIntOp rv1 rv2 = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    case trv1 of
        TNoref (Tclean (Tcomp (Tprim (Tint _)))) -> return ()
        _ -> throwError $ ExpectedInteger trv1

    checkTypes trv1 trv2
    return trv1

-- Check if rvalues have equal, clean int/char type and return it.
tcRVIntOrCharType :: RValue -> RValue -> TC Type
tcRVIntOrCharType rv1 rv2 = do
    trv1 <- tcRV rv1
    trv2 <- tcRV rv2
    case trv1 of
        TNoref (Tclean (Tcomp (Tprim Tchar))) -> return ()
        TNoref (Tclean (Tcomp (Tprim (Tint _)))) -> return ()
        _ -> throwError $ ExpectedOrdering trv1

    checkTypes trv1 trv2
    return trv1

tcRVIntervalType :: Interval -> TC Type
tcRVIntervalType (IntervalII rv1 rv2) = tcRVIntOrCharType rv1 rv2
tcRVIntervalType (IntervalIE rv1 rv2) = tcRVIntOrCharType rv1 rv2
tcRVIntervalType (IntervalEI rv1 rv2) = tcRVIntOrCharType rv1 rv2
tcRVIntervalType (IntervalEE rv1 rv2) = tcRVIntOrCharType rv1 rv2

declareArgsT :: [Arg] -> TC TCEnv
declareArgsT [] = ask
declareArgsT ((FArg id t):l) = do
    env <- setLVType (LVId id) t
    runWithTCEnv env (declareArgsT l)

fArgsType :: [Arg] -> Type
fArgsType args = argsType $ fArgsTypes args

fArgsTypes :: [Arg] -> [Type]
fArgsTypes [] = []
fArgsTypes ((FArg _ t):l) = t : fArgsTypes l
