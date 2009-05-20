module SimplyTyped.Types where
  import Interpreter.Types

  data ITerm
     =  Ann    CTerm Type
     |  Bound  Int String --should not be needed
     |  Free   Name
     |  ITerm :@: CTerm
    deriving (Show{--, Eq--})

 
  instance Eq ITerm where
    Ann x y == Ann x' y' = x==x' && y==y'
    Bound n1 _ == Bound n2 _ = n1==n2
    Free n == Free n' = n==n'
    a :@: b == a':@:b' = a==a' && b==b'
    _ == _ = False 


  data CTerm
     =  Inf  ITerm 
     |  Lam  String CTerm
    deriving (Show, Eq)
 


{- LINE 705 "LP.lhs" #-}
  data Type
     =  TFree  Name
     |  Fun    Type Type
    deriving (Show, Eq)
{- LINE 712 "LP.lhs" #-}
  data Value
     =  VLam  String    (Value -> Value)
     |  VNeutral  Neutral
{- LINE 725 "LP.lhs" #-}
  data Neutral
     =  NFree  Name
     |  NApp   Neutral Value
{- LINE 732 "LP.lhs" #-}
  vfree :: Name -> Value
  vfree n = VNeutral (NFree n)
{- LINE 786 "LP.lhs" #-}
  data Kind = Star
    deriving (Show)
 
  data Info
     =  HasKind  Kind
     |  HasType  Type 
    deriving (Show)
 
  type Context = [(Name, Info)]
{- LINE 801 "LP.lhs" #-}
  type Env = [Value]





