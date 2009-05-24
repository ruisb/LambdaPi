module Main where
import LambdaPi.Interpreter
import Interpreter.Types

main :: IO ()
main = repLP ctx True

ctx = IntCtx {readline = const $ do
                           x <- getLine
                           return $ Just x,
       addHistory = const $ return ()}



