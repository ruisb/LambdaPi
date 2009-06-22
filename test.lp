
-- simple
data Nat :: * where
   z :: Nat,
   s :: Nat -> Nat

let i   = s z
let ii  = s i
let iii = s ii
let iv  = s iii
let v   = s iv

data Nat2 :: * where
    z2 :: Nat2,
    s2 :: forall (x :: Nat2) . Nat2

let to2   = NatElim  (\_ -> Nat2) z2 (\_ n -> s2 n) :: Nat -> Nat2
let from2 = Nat2Elim (\_ -> Nat ) z  (\_ n -> s  n) :: Nat2 -> Nat

let plus  = (\x y -> NatElim  (\_ -> Nat ) y (\_ g -> s g) x)     :: Nat -> Nat -> Nat
let mult  = (\x y -> NatElim  (\_ -> Nat ) y (\_ g -> plus g y) x)  :: Nat -> Nat -> Nat
let plus2 = (\x y -> Nat2Elim (\_ -> Nat2) y (\_ g -> s2 g) x)    :: Nat2 -> Nat2 -> Nat2
let plus2 = (\x y -> Nat2Elim (\_ -> Nat2) y (\_ g -> plus2 g y) x) :: Nat2 -> Nat2 -> Nat2


------polymorphic
--data List :: * ->  * where 
--  nil  :: forall (A :: *) . List A,
--  cons :: forall (A :: *) . A -> List A -> List A

--dependent
data Vec :: * -> Nat -> * where
  vnil  :: forall (A :: *) . Vec A z,
  vcons :: forall (A :: *) (n :: Nat) . A -> Vec A n -> Vec A (s n)

--data Fin :: Nat -> * where 
--  fzero :: forall (n :: Nat) . Fin (s n),
--  fsucc :: forall (n :: Nat) . Fin n -> Fin (s n)



