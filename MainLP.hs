module Main where
import LambdaPi.Interpreter
import Interpreter.Types
import System.Environment (getArgs)
import Debug.Trace -- FIMXE temp

main :: IO ()
main = do
  args <- getArgs
  -- If there are arguments, assume the first one is a filepath.
  repLP True (if length args > 0 then Just $ head args else Nothing)

