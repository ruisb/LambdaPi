module LambdaPi.Types where
  import Interpreter.Types




  data CTerm_
     =  Inf_  ITerm_
     |  Lam_  String CTerm_
{- LINE 2 "CTerm_Nat.lhs" #-}
     |  Zero_
     |  Succ_ CTerm_
{- LINE 2 "CTerm_Vec.lhs" #-}
    |  Nil_ CTerm_
    |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_
{- LINE 2 "CTerm_Eq.lhs" #-}
     |  Refl_ CTerm_ CTerm_
{- LINE 2 "CTerm_Fin.lhs" #-}
    |  FZero_ CTerm_
    |  FSucc_ CTerm_ CTerm_
{- LINE 1523 "LP.lhs" #-}
    deriving (Show, Eq)
{- LINE 1548 "LP.lhs" #-}
  data ITerm_
     =  Ann_ CTerm_ CTerm_
     |  Star_
     |  Pi_ String CTerm_ CTerm_
     |  Bound_  Int String
     |  Free_  Name
     |  ITerm_ :$: CTerm_
{- LINE 2 "ITerm_Nat.lhs" #-}
     |  Nat_
     |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_
{- LINE 2 "ITerm_Vec.lhs" #-}
    |  Vec_ CTerm_ CTerm_
    |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
{- LINE 2 "ITerm_Eq.lhs" #-}
     |  Eq_ CTerm_ CTerm_ CTerm_
     |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
{- LINE 2 "ITerm_Fin.lhs" #-}
     |  Fin_ CTerm_
     |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
{- LINE 1564 "LP.lhs" #-}
    deriving (Show{--, Eq--})
{- LINE 1569 "LP.lhs" #-}


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
{- LINE 2 "Value_Nat.lhs" #-}
    |  VNat_
    |  VZero_
    |  VSucc_ Value_
{- LINE 2 "Value_Vec.lhs" #-}
    |  VNil_ Value_
    |  VCons_ Value_ Value_ Value_ Value_
    |  VVec_ Value_ Value_
{- LINE 2 "Value_Eq.lhs" #-}
    |  VEq_ Value_ Value_ Value_
    |  VRefl_ Value_ Value_
{- LINE 2 "Value_Fin.lhs" #-}
    |  VFZero_ Value_
    |  VFSucc_ Value_ Value_
    |  VFin_ Value_
{- LINE 1582 "LP.lhs" #-}
  data Neutral_
     =  NFree_  Name
     |  NApp_  Neutral_ Value_
{- LINE 2 "Neutral_Nat.lhs" #-}
    |  NNatElim_ Value_ Value_ Value_ Neutral_
{- LINE 2 "Neutral_Vec.lhs" #-}
    |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
{- LINE 2 "Neutral_Eq.lhs" #-}
    |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
{- LINE 2 "Neutral_Fin.lhs" #-}
    |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_
{- LINE 1620 "LP.lhs" #-}
  type Env_ = [Value_]


