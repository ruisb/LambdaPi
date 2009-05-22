module LambdaPi.Types where
import Interpreter.Types

data CTerm_
   =  Inf_  ITerm_
   |  Lam_  String CTerm_
   |  Zero_
   |  Succ_ CTerm_
   |  Nil_ CTerm_
   |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Refl_ CTerm_ CTerm_
   |  FZero_ CTerm_
   |  FSucc_ CTerm_ CTerm_
  deriving (Show, Eq)

data ITerm_
   =  Ann_ CTerm_ CTerm_
   |  Star_
   |  Pi_ String CTerm_ CTerm_
   |  Bound_  Int String
   |  Free_  Name
   |  ITerm_ :$: CTerm_
   |  Nat_
   |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Vec_ CTerm_ CTerm_
   |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Eq_ CTerm_ CTerm_ CTerm_
   |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Fin_ CTerm_
   |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
  deriving (Show{--, Eq--})

instance Eq ITerm_ where
  Ann_ x y == Ann_ x' y' = x==x' && y==y'
  Star_ == Star_ = True
  Pi_ _ a b == Pi_ _ a' b' = a==a' && b==b'
  Bound_ n1 _ == Bound_ n2 _ = n1==n2
  Free_ n == Free_ n' = n==n'
  a :$: b == a':$:b' = a==a' && b==b'
  Nat_ == Nat_ = True
  NatElim_ a b c d == NatElim_ a' b' c' d' = a==a' && b==b' && c == c' && d == d'
  Vec_ a b == Vec_ a' b' = a==a' && b ==b'
  VecElim_ a b c d e f == VecElim_ a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
  Eq_ a b c == Eq_ a' b' c' = a==a' && b==b' && c==c'
  EqElim_ a b c d e f == EqElim_ a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
  Fin_ a == Fin_ a' = a==a'
  FinElim_ a b c d e == FinElim_ a' b' c' d' e' = a==a' && b==b' && c == c' && d == d' && e == e'
  _ == _ = False 

data Value_
   =  VLam_ String (Value_ -> Value_)
   |  VStar_
   |  VPi_ String Value_ (Value_ -> Value_)
   |  VNeutral_ Neutral_
   |  VNat_
   |  VZero_
   |  VSucc_ Value_
   |  VNil_ Value_
   |  VCons_ Value_ Value_ Value_ Value_
   |  VVec_ Value_ Value_
   |  VEq_ Value_ Value_ Value_
   |  VRefl_ Value_ Value_
   |  VFZero_ Value_
   |  VFSucc_ Value_ Value_
   |  VFin_ Value_

data Neutral_
   =  NFree_  Name
   |  NApp_  Neutral_ Value_
   |  NNatElim_ Value_ Value_ Value_ Neutral_
   |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
   |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
   |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_

type Env_ = [Value_]