

let ofLen = natElim (\n -> Vec Unit n) 
                    (Nil Unit)
                    (\ n t -> Cons Unit n U t) 


let f = (\ t x -> (Cons t 0 x (Nil t :: Vec t 0)) :: Vec t 1)  :: forall (t :: *) (x :: t) . Vec t 1


let ty = (\ n -> Vec Unit n)  ::   Nat -> * 

let k = ofLen :: forall (n :: Nat) . ty n 



