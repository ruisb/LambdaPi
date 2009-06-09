data Nat2 :: * where
  Zero2 :: Nat2,
  Suc2 :: Nat2 -> Nat2
  --FIXME temp with , seperated


let plus =
  natElim
    ( \ _ -> Nat2 -> Nat2 )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ