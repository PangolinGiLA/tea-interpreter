module TypeCheckUtils where

import Data.Map (empty)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

import Syntax.Abs (Type(..), TypeNoref(..), TInt(..), Stmt(..), SBlock(..), CIdent(..), StringLiteral(..), SIf(..), RValue(..), TInt(..), Decl(..), VDecl(..), FDecl(..), Arg(..), LValue(..), IndexedArr(..), Interval(..), TypeNoref, TClean (..), TComp (..), TPrim (..), TFuns (..), TypeRef (..))

import Utils (mapHas, mapGet, mapSet)
import TCTypes
import VMTypes (TEnv)

-- Custom equality for `Type` which ignores position in identifiers.
equalT :: Type -> Type -> Bool
equalT t1 t2 =
    case (t1, t2) of
        (TRef (Tref tc1), TRef (Tref tc2)) -> equalTClean tc1 tc2
        (TRef (Tcref tc1), TRef (Tcref tc2)) -> equalTClean tc1 tc2
        (TNoref (Tclean tc1), TNoref (Tclean tc2)) -> equalTClean tc1 tc2
        (TNoref (Tconst tc1), TNoref (Tconst tc2)) -> equalTClean tc1 tc2
        _ -> False

equalTClean :: TClean -> TClean -> Bool
-- Special rule for identifiers.
equalTClean (Talias (CIdent (_, n1))) (Talias (CIdent (_, n2))) = n1 == n2
-- The identifiers rule must be used in all subcontexts.
equalTClean (Tcomp t1) (Tcomp t2) =
    case (t1, t2) of
        (Tarr tp1, Tarr tp2) -> equalT tp1 tp2

        (Ttup tp1 tplist1, Ttup tp2 tplist2) ->
            and $ zipWith equalT (tp1:tplist1) (tp2:tplist2)

        (Tfun (TFun targs1 tret1), Tfun (TFun targs2 tret2)) ->
            equalT targs1 targs2 && equalT tret1 tret2

        _ -> t1 == t2

-- Default for all others.
equalTClean t1 t2 = t1 == t2

signalWarn :: TCWarning -> TC ()
signalWarn w = tell [TCWarn w]

runTC :: TC a -> TCEnv -> (Either TCError a, [TCDiag])
runTC tc env = runIdentity $ runReaderT (runWriterT (runExceptT tc)) env

---------- TC Environment utils ----------

initialTCEnv :: TCEnv
initialTCEnv = CTCEnv { tvEnv = Data.Map.empty, taEnv = Data.Map.empty, ret = Nothing }

runWithTCEnv :: TCEnv -> TC a -> TC a
runWithTCEnv env tc = do
    local (const env) tc

-- Make a TCEnv with a new TVEnv.
makeTCEnvV :: TVEnv -> TC TCEnv
makeTCEnvV tvEnv = do
    currTAEnv <- asks taEnv
    currRet <- asks ret
    return $ CTCEnv { tvEnv = tvEnv, taEnv = currTAEnv, ret = currRet }

-- Make a TCEnv with a new TEnv.
makeTCEnvA :: TEnv -> TC TCEnv
makeTCEnvA taEnv = do
    currTVEnv <- asks tvEnv
    currRet <- asks ret
    return $ CTCEnv { tvEnv = currTVEnv, taEnv = taEnv, ret = currRet }

-- Add a return value to the provided TCEnv.
makeTCEnvF :: TCEnv -> Type -> TCEnv
makeTCEnvF fenv tret =
    let currTAEnv = taEnv fenv in
    let currTVEnv = tvEnv fenv in
        CTCEnv { tvEnv = currTVEnv, taEnv = currTAEnv, ret = Just tret }

-- See whether the variable is already in the environment.
hasVar :: CIdent -> TC Bool
hasVar (CIdent (_, name)) = do
    venv <- asks tvEnv
    return $ mapHas venv name

getVarType :: CIdent -> TC Type
getVarType (CIdent (pos, name)) = do
    venv <- asks tvEnv
    if mapHas venv name
        then return $ mapGet venv name
        else throwError $ UndeclaredVar pos name

-- Append the current environment with a new variable.
newTCEnv :: CIdent -> Type -> TC TCEnv
newTCEnv id t = do
    let CIdent (pos, name) = id
    alreadyDeclared <- hasVar id
    -- Shadowing warning only if the variable had previously the same type.
    when alreadyDeclared
        (do
            oldType <- getVarType id
            when (equalT t oldType)
                (signalWarn (Shadowing pos name))
        )
    
    -- Update the environment.
    currMap <- asks tvEnv
    let newMap = mapSet currMap name t
    makeTCEnvV newMap

getAliasType :: CIdent -> TC TClean
getAliasType (CIdent (pos, name)) = do
    aenv <- asks taEnv
    if mapHas aenv name
        then return $ Tcomp $ mapGet aenv name
        else throwError $ UndeclaredAlias pos name

---------- Type constructors and destructors ----------

boolType :: Type
boolType = compType (Tprim Tbool)

usizeType :: Type
usizeType = compType (Tprim (Tint Ti64))

voidType :: Type
voidType = compType (Tprim Tvoid)

charType :: Type
charType = compType (Tprim Tchar)

stringType :: Type
stringType = compType Tstr

defaultIntType :: Type
defaultIntType = compType (Tprim (Tint Ti64))

tupleType :: Type -> [Type] -> Type
tupleType t1 tt = compType (Ttup t1 tt)

arrType :: Type -> Type
arrType t = compType (Tarr t)

aliasType :: CIdent -> Type
aliasType t = TNoref (Tclean (Talias t))

cleanType :: TClean -> Type
cleanType t = TNoref (Tclean t)

compType :: TComp -> Type
compType t = cleanType (Tcomp t)

argsType :: [Type] -> Type
argsType [] = voidType
argsType [t] = t
argsType (t1:tt) = tupleType t1 tt

stripClean :: Type -> TClean
stripClean (TNoref (Tclean t)) = t
stripClean (TNoref (Tconst t)) = t
stripClean (TRef (Tref t)) = t
stripClean (TRef (Tcref t)) = t

---------- Checkers ----------

checkTypes :: Type -> Type -> TC ()
checkTypes expected given =
    unless (equalT expected given) (
        throwError $ TypeMismatch expected given)

checkAssgnTypes :: Type -> Type -> TC ()
-- Special case for "ref = clean".
checkAssgnTypes (TRef (Tref t1)) (TNoref (Tclean t2)) =
    unless (equalTClean t1 t2) (
        throwError $ TypeMismatch (TRef (Tref t1)) (TNoref (Tclean t2))
    )
-- All else as default.
checkAssgnTypes t1 t2 = checkTypes t1 t2

checkSizeType :: Type -> TC ()
checkSizeType (TNoref (Tclean (Tcomp (Tprim (Tint Ti64))))) = return ()
checkSizeType t = throwError $ SizeIsI64 t

checkTypeExists :: Type -> TC ()
checkTypeExists t = checkTypeCleanExists (stripClean t)

checkTypeCleanExists :: TClean -> TC ()
checkTypeCleanExists (Tcomp t) =
    case t of
        Tarr tp -> checkTypeExists tp
        Ttup tp tplist -> do
            when (null tplist) (
                throwError InvalidTupleSize)
            mapM_ checkTypeExists (tp:tplist)
        Tfun (TFun targs tret) -> do
            checkTypeExists targs
            checkTypeExists tret
        _ -> return ()

checkTypeCleanExists (Talias cid) = do
    _ <- getAliasType cid
    -- If we have an alias in the environment, then
    -- it must point to an existing type, so no need
    -- to check recursively.
    return ()

checkMut :: Type -> TC ()
checkMut (TNoref (Tclean t)) = return ()
checkMut (TNoref (Tconst t)) = throwError $ ConstViolation (TNoref (Tconst t))
checkMut (TRef (Tref t)) = return ()
checkMut (TRef (Tcref t)) = throwError $ ConstViolation (TRef (Tcref t))

checkNoref :: Type -> TC ()
checkNoref (TRef t) = throwError $ UninitRef (TRef t)
checkNoref (TNoref t) = do
    let tclean = stripClean (TNoref t)
    case tclean of
        Tcomp tcomp -> 
            case tcomp of
                Ttup tp tplist ->
                    mapM_ checkNoref (tp:tplist)
                _ -> return ()
        Talias cid -> do
            realType <- getAliasType cid
            -- An alias may point to a type with a reference
            -- inside (e.g. (ref i64, i64)), so we need to check
            -- recursively.
            checkNoref $ TNoref (Tclean realType)

assertEqCast :: TCError -> Type -> Type -> TC ()
assertEqCast err t1 t2 = unless (equalT t1 t2) (throwError err)

assertEqCastClean :: TCError -> TClean -> TClean -> TC ()
assertEqCastClean err t1 t2 = unless (equalTClean t1 t2) (throwError err)

checkCast :: Type -> Type -> TC ()
checkCast to from = do
    let err = InvalidCast to from
    case (to, from) of
        (TRef (Tcref t1), TRef (Tref t2)) ->
            -- References cannot cast the underlying type.
            assertEqCastClean err t1 t2

        -- Can cast clean <-> const freely with the underlying type.
        (TNoref (Tclean t1), TNoref (Tconst t2)) ->
            checkCastClean err t1 t2
        (TNoref (Tconst t1), TNoref (Tclean t2)) ->
            checkCastClean err t1 t2
        
        -- Can cast the underlying type under const or clean.
        (TNoref (Tclean t1), TNoref (Tclean t2)) ->
            checkCastClean err t1 t2
        (TNoref (Tconst t1), TNoref (Tconst t2)) ->
            checkCastClean err t1 t2

        _ ->
            assertEqCast err to from

checkCastClean :: TCError -> TClean -> TClean -> TC ()
-- Resolve aliases.
checkCastClean err (Talias id) from = do
    tal <- getAliasType id
    checkCastClean err tal from
checkCastClean err to (Talias id) = do
    tal <- getAliasType id
    checkCastClean err to tal

-- Clean tuple cast depends on its components.
checkCastClean err (Tcomp (Ttup t1To ttTo)) (Tcomp (Ttup t1From ttFrom)) =
    zipWithM_ checkCast (t1To:ttTo) (t1From:ttFrom)

-- Can cast between integers.
checkCastClean err (Tcomp (Tprim (Tint to))) (Tcomp (Tprim (Tint from))) =
    return ()

-- Otherwise, only cast when no change is made to the type.
checkCastClean err to from = assertEqCastClean err to from

---------- Assuming decompositions ----------

assumeIndexed :: Type -> TC Type
assumeIndexed t =
    -- An array can always be indexed.
    let tc = stripClean t in
    case tc of
        Tcomp (Tarr tel) -> return tel
        Tcomp Tstr -> return charType
        _ -> throwError $ ExpectedArr t

assumeFun :: Type -> TC (Type, Type)
assumeFun fun =
    -- A function can always be called.
    let func = stripClean fun in
    case func of
        Tcomp (Tfun (TFun targs tret)) -> return (targs, tret)
        _ -> throwError $ ExpectedFun fun