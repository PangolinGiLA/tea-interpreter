module Main where

import Interpreter (compute)
import System.Environment (getArgs)
import System.IO
import Control.Monad

main :: IO ()
main = do
    args <- getArgs

    if length args /= 1
        then do
            let useStr = "Use: ./interpreter <program.tea>"
            putStrLn $ "Invalid number of arguments. " ++ useStr
            return ()
        else do
            let program = head args
            readFile program >>= compute