module Interpreter.Types where

data IntCtx = IntCtx {readline :: String -> IO (Maybe String), addHistory :: String -> IO ()}

type Name  = String

type Result a = Either String a

type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
  deriving (Show)
