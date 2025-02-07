module Interpreter where

import System.Exit (exitFailure)
import System.IO
import Control.Monad

import VMTypes
import TCTypes
import Syntax.Lex   ( Token, mkPosToken )
import Syntax.Par   ( pStmt, myLexer )
import Syntax.Print ( Print, printTree )
import Syntax.Skel  ()

import InterpretNode ( iS )
import VMUtils       ( initialEnv, initialStore, runVM )
import PrintUtils ( printDiag, printTCDiag )
import TypeCheckNode ( tcS )
import TypeCheckUtils ( runTC, initialTCEnv )

writeLogs :: [Log] -> IO ()
writeLogs = mapM_ printStdout
  where
    printStdout (Stdout msg) = putStrLn msg
    printStdout (Stderr diag) = hPutStrLn stderr $ printDiag diag

addError :: Either DiffCFlow () -> [Log] -> IO [Log]
addError (Right _) logs = return logs
addError (Left (Right ret)) logs = return $ logs ++ [Stderr (Err (UncaughtReturnValue ret))]
addError (Left (Left err)) logs = return $ logs ++ [Stderr (Err err)]

addTCError :: Either TCError Bool -> [TCDiag] -> IO [TCDiag]
addTCError (Right _) diag = return diag
addTCError (Left err) diag = return $ diag ++ [TCErr err]

writeTCDiag :: [TCDiag] -> IO ()
writeTCDiag = mapM_ (hPutStrLn stderr . printTCDiag)

isTCError :: TCDiag -> Bool
isTCError (TCErr _) = True
isTCError (TCWarn _) = False

compute :: String -> IO ()
compute s =
    case pStmt (myLexer s) of
        Left err -> do
            putStrLn "\nParse              Failed...\n"
            putStrLn err
            exitFailure
        Right stmt -> do
            let tcenv = initialTCEnv
            let result = runTC(tcS stmt) tcenv
            let (ret, diag) = result
            diag <- addTCError ret diag
            writeTCDiag diag
            unless (any isTCError diag) (do
                let env = initialEnv
                let store = initialStore
                let result = runVM (iS stmt) env store

                let ((ret, logs), _) = result
                logs <- addError ret logs
                writeLogs logs)
