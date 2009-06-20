module Interpreter.Types where
import Data.Map (Map)



type Name  = String

-- The result of an action. Or succes, or fail with a message.
type Result a = Either String a

type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String, tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
                 | DataDecl (DataInfo tinf)
  deriving (Show)


data DataInfo tinf = DataInfo {name :: String, sig :: tinf, ctors :: Map String tinf} 
   deriving Show
                                                   -- Data <datatype name> <datatype dependent space>
                                                   -- mapping: Ctor-name -> type.

