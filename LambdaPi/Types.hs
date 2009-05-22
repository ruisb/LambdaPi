module LambdaPi.Types where
import Interpreter.Types

data CTerm
   =  Inf  ITerm
   |  Lam  String CTerm
   |  Zero
   |  Succ CTerm
   |  Nil CTerm
   |  Cons CTerm CTerm CTerm CTerm
   |  Refl CTerm CTerm
   |  FZero CTerm
   |  FSucc CTerm CTerm
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Star
   |  Pi String CTerm CTerm
   |  Bound  Int 
   |  Free  Name
   |  ITerm :$: CTerm
   |  Nat
   |  NatElim CTerm CTerm CTerm CTerm
   |  Vec CTerm CTerm
   |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Eq CTerm CTerm CTerm
   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Fin CTerm
   |  FinElim CTerm CTerm CTerm CTerm CTerm
  deriving (Show{--, Eq--})

instance Eq ITerm where
  Ann x y == Ann x' y' = x==x' && y==y'
  Star == Star = True
  Pi _ a b == Pi _ a' b' = a==a' && b==b'
  Bound n1 == Bound n2 = n1==n2
  Free n == Free n' = n==n'
  a :$: b == a':$:b' = a==a' && b==b'
  Nat == Nat = True
  NatElim a b c d == NatElim a' b' c' d' = a==a' && b==b' && c == c' && d == d'
  Vec a b == Vec a' b' = a==a' && b ==b'
  VecElim a b c d e f == VecElim a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
  Eq a b c == Eq a' b' c' = a==a' && b==b' && c==c'
  EqElim a b c d e f == EqElim a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
  Fin a == Fin a' = a==a'
  FinElim a b c d e == FinElim a' b' c' d' e' = a==a' && b==b' && c == c' && d == d' && e == e'
  _ == _ = False 


data Value
   =  VLam String (Value -> Value)
   |  VStar
   |  VPi String Value (Value -> Value)
   |  VNeutral Neutral
   |  VNat
   |  VZero
   |  VSucc Value
   |  VNil Value
   |  VCons Value Value Value Value
   |  VVec Value Value
   |  VEq Value Value Value
   |  VRefl Value Value
   |  VFZero Value
   |  VFSucc Value Value
   |  VFin Value

data Neutral
   =  NFree  Name
   |  NQuote Int 
   |  NApp  Neutral Value
   |  NNatElim Value Value Value Neutral
   |  NVecElim Value Value Value Value Value Neutral
   |  NEqElim Value Value Value Value Value Neutral
   |  NFinElim Value Value Value Value Neutral

type Env = [Value]
