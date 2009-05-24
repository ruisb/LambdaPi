module Main where
import LambdaPi.Interpreter
import Interpreter.Types
import qualified System.Console.Readline as R

main :: IO ()
main = repLP ctx True



ctx = IntCtx {readline = R.readline, addHistory = R.addHistory}



