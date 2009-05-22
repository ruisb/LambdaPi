module Interpreter.Types where

-- data Name
--    =  Global  String
--  --  |  Local   Int  String
-- --   |  Quote   Int  String  --should not be needed
--   deriving (Show {--, Eq--})
-- 
-- instance Eq Name where
--   (Global s1) == (Global s2) = s1 == s2
--  -- (Local n1 _) == (Local n2 _) = n1==n2
-- --  (Quote n1 _) == (Quote n2 _) = n1 == n2
--   _ == _ = False

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
