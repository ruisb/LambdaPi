module LambdaPi.Functions where
  import Interpreter.Types
  import LambdaPi.Types
  import LambdaPi.Printer
  
  import Control.Monad.Error
  import Text.PrettyPrint.HughesPJ hiding (parens)
  
{- LINE 176 "LP.lhs" #-}
  putstrln x = putStrLn x


 
  vapp_ :: Value_ -> Value_ -> Value_
  vapp_ (VLam_ _ f)    v  =  f v
  vapp_ (VNeutral_ n)  v  =  VNeutral_ (NApp_ n v)
 
  vfree_ :: Name -> Value_
  vfree_ n = VNeutral_ (NFree_ n)
 
  cEval_ :: CTerm_ -> (NameEnv Value_,Env_) -> Value_
  cEval_ (Inf_  ii)    d  =  iEval_ ii d
  cEval_ (Lam_ vn c)    d  =  VLam_ vn (\ x -> cEval_ c (((\(e, d) -> (e,  (x : d))) d)))
{- LINE 2 "cEval_Nat.lhs" #-}
  cEval_ Zero_      d  = VZero_
  cEval_ (Succ_ k)  d  = VSucc_ (cEval_ k d)
{- LINE 2 "cEval_Vec.lhs" #-}
  cEval_ (Nil_ a)          d  =  VNil_ (cEval_ a d)
  cEval_ (Cons_ a n x xs)  d  =  VCons_  (cEval_ a d) (cEval_ n d)
                                         (cEval_ x d) (cEval_ xs d)
{- LINE 2 "cEval_Eq.lhs" #-}
  cEval_ (Refl_ a x)       d  =  VRefl_ (cEval_ a d) (cEval_ x d)
{- LINE 2 "cEval_Fin.lhs" #-}
  cEval_ (FZero_ n)    d  =  VFZero_ (cEval_ n d)
  cEval_ (FSucc_ n f)  d  =  VFSucc_ (cEval_ n d) (cEval_ f d)
{- LINE 1654 "LP.lhs" #-}
  iEval_ :: ITerm_ -> (NameEnv Value_,Env_) -> Value_
  iEval_ (Ann_  c _)       d  =  cEval_ c d
{- LINE 1659 "LP.lhs" #-}
  iEval_ Star_           d  =  VStar_   
  iEval_ (Pi_ vn ty ty') d  =  VPi_ vn (cEval_ ty d) (\ x -> cEval_ ty' (((\(e, d) -> (e,  (x : d))) d)))   
{- LINE 1664 "LP.lhs" #-}
  iEval_ (Free_  x)      d  =  case lookup x (fst d) of Nothing ->  (vfree_ x); Just v -> v 
  iEval_ (Bound_  ii _)  d  =  (snd d) !! ii
  iEval_ (i :$: c)       d  =  vapp_ (iEval_ i d) (cEval_ c d)
{- LINE 2 "iEval_Nat.lhs" #-}
  iEval_ Nat_                  d  =  VNat_
  iEval_ (NatElim_ m mz ms n)  d 
    =  let  mzVal = cEval_ mz d
            msVal = cEval_ ms d
            rec nVal =
              case nVal of
                VZero_       ->  mzVal
                VSucc_ k     ->  msVal `vapp_` k `vapp_` rec k
                VNeutral_ n  ->  VNeutral_
                                 (NNatElim_ (cEval_ m d) mzVal msVal n)
                _            ->  error "internal: eval natElim"
       in   rec (cEval_ n d)
{- LINE 3 "iEval_Vec.lhs" #-}
  iEval_ (Vec_ a n)                 d  =  VVec_ (cEval_ a d) (cEval_ n d)
{- LINE 7 "iEval_Vec.lhs" #-}
  iEval_ (VecElim_ a m mn mc n xs)  d  =
    let  mnVal  =  cEval_ mn d
         mcVal  =  cEval_ mc d
         rec nVal xsVal =
           case xsVal of
             VNil_ _          ->  mnVal
             VCons_ _ k x xs  ->  foldl vapp_ mcVal [k, x, xs, rec k xs]
             VNeutral_ n      ->  VNeutral_
                                  (NVecElim_  (cEval_ a d) (cEval_ m d)
                                              mnVal mcVal nVal n)
             _                ->  error "internal: eval vecElim"
    in   rec (cEval_ n d) (cEval_ xs d)
{- LINE 2 "iEval_Eq.lhs" #-}
  iEval_ (Eq_ a x y)                d  =  VEq_ (cEval_ a d) (cEval_ x d) (cEval_ y d)
  iEval_ (EqElim_ a m mr x y eq)    d  =
    let  mrVal  =  cEval_ mr d
         rec eqVal =
           case eqVal of
             VRefl_ _ z -> mrVal `vapp_` z
             VNeutral_ n ->  
               VNeutral_ (NEqElim_  (cEval_ a d) (cEval_ m d) mrVal
                                    (cEval_ x d) (cEval_ y d) n)
             _ -> error "internal: eval eqElim"
    in   rec (cEval_ eq d)
{- LINE 2 "iEval_Fin.lhs" #-}
  iEval_ (Fin_ n)                d  =  VFin_ (cEval_ n d)
  iEval_ (FinElim_ m mz ms n f)  d  =
    let  mzVal  =  cEval_ mz d
         msVal  =  cEval_ ms d
         rec fVal =
           case fVal of
             VFZero_ k        ->  mzVal `vapp_` k
             VFSucc_ k g      ->  foldl vapp_ msVal [k, g, rec g]
             VNeutral_ n'     ->  VNeutral_
                                  (NFinElim_  (cEval_ m d) (cEval_ mz d)
                                              (cEval_ ms d) (cEval_ n d) n')
             _                ->  error "internal: eval finElim"
    in   rec (cEval_ f d)
{- LINE 1679 "LP.lhs" #-}
  iSubst_ :: Int -> ITerm_ -> ITerm_ -> ITerm_
  iSubst_ ii i'   (Ann_ c c')     =  Ann_ (cSubst_ ii i' c) (cSubst_ ii i' c')
{- LINE 1684 "LP.lhs" #-}
  
  iSubst_ ii r  Star_           =  Star_  
  iSubst_ ii r  (Pi_ vn ty ty') =  Pi_ vn (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')
{- LINE 1690 "LP.lhs" #-}
  iSubst_ ii i' (Bound_ j vn)   =  if ii == j then i' else Bound_ j vn
  iSubst_ ii i' (Free_ y)       =  Free_ y
  iSubst_ ii i' (i :$: c)       =  iSubst_ ii i' i :$: cSubst_ ii i' c
{- LINE 2 "iSubst_Nat.lhs" #-}
  iSubst_ ii r  Nat_            =  Nat_
  iSubst_ ii r  (NatElim_ m mz ms n)
                                =  NatElim_ (cSubst_ ii r m)
                                            (cSubst_ ii r mz) (cSubst_ ii r ms)
                                            (cSubst_ ii r ms)
{- LINE 2 "iSubst_Vec.lhs" #-}
  iSubst_ ii r  (Vec_ a n)      =  Vec_ (cSubst_ ii r a) (cSubst_ ii r n)
  iSubst_ ii r  (VecElim_ a m mn mc n xs)
                                =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                            (cSubst_ ii r mn) (cSubst_ ii r mc)
                                            (cSubst_ ii r n) (cSubst_ ii r xs)
{- LINE 2 "iSubst_Eq.lhs" #-}
  iSubst_ ii r  (Eq_ a x y)     =  Eq_ (cSubst_ ii r a)
                                       (cSubst_ ii r x) (cSubst_ ii r y)
  iSubst_ ii r  (EqElim_ a m mr x y eq)
                                =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                            (cSubst_ ii r mr) (cSubst_ ii r x)
                                            (cSubst_ ii r y) (cSubst_ ii r eq)
{- LINE 2 "iSubst_Fin.lhs" #-}
  iSubst_ ii r  (Fin_ n)        =  Fin_ (cSubst_ ii r n)
  iSubst_ ii r  (FinElim_ m mz ms n f)
                                =  FinElim_ (cSubst_ ii r m)
                                            (cSubst_ ii r mz) (cSubst_ ii r ms)
                                            (cSubst_ ii r n) (cSubst_ ii r f)
{- LINE 1701 "LP.lhs" #-}
  cSubst_ :: Int -> ITerm_ -> CTerm_ -> CTerm_
  cSubst_ ii i' (Inf_ i)      =  Inf_ (iSubst_ ii i' i)
  cSubst_ ii i' (Lam_ vn c)   =  Lam_ vn (cSubst_ (ii + 1) i' c)
--PROBLEM:CAPTURE?
{- LINE 2 "cSubst_Nat.lhs" #-}
  cSubst_ ii r  Zero_         =  Zero_
  cSubst_ ii r  (Succ_ n)     =  Succ_ (cSubst_ ii r n)
{- LINE 2 "cSubst_Vec.lhs" #-}
  cSubst_ ii r  (Nil_ a)      =  Nil_ (cSubst_ ii r a)
  cSubst_ ii r  (Cons_ a n x xs)
                              =  Cons_ (cSubst_ ii r a) (cSubst_ ii r x)
                                       (cSubst_ ii r x) (cSubst_ ii r xs)
{- LINE 2 "cSubst_Eq.lhs" #-}
  cSubst_ ii r  (Refl_ a x)   =  Refl_ (cSubst_ ii r a) (cSubst_ ii r x)
{- LINE 2 "cSubst_Fin.lhs" #-}
  cSubst_ ii r  (FZero_ n)    =  FZero_ (cSubst_ ii r n)
  cSubst_ ii r  (FSucc_ n k)  =  FSucc_ (cSubst_ ii r n) (cSubst_ ii r k)
{- LINE 1712 "LP.lhs" #-}
  quote_ :: Int -> Value_ -> CTerm_
  quote_ ii (VLam_ vn t)
    =     Lam_ vn (quote_ (ii + 1) (t (vfree_ (Quote ii vn))))
{- LINE 1718 "LP.lhs" #-}
  
  quote_ ii VStar_ = Inf_ Star_ 
  quote_ ii (VPi_ vn v f)                                       
      =  Inf_ (Pi_ vn (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii vn )))))  
{- LINE 1725 "LP.lhs" #-}
  quote_ ii (VNeutral_ n)
    =     Inf_ (neutralQuote_ ii n)
{- LINE 2 "quote_Nat.lhs" #-}
  quote_ ii VNat_       =  Inf_ Nat_
  quote_ ii VZero_      =  Zero_
  quote_ ii (VSucc_ n)  =  Succ_ (quote_ ii n)
{- LINE 2 "quote_Vec.lhs" #-}
  quote_ ii (VVec_ a n)         =  Inf_ (Vec_ (quote_ ii a) (quote_ ii n))
  quote_ ii (VNil_ a)           =  Nil_ (quote_ ii a)
  quote_ ii (VCons_ a n x xs)   =  Cons_  (quote_ ii a) (quote_ ii n)
                                          (quote_ ii x) (quote_ ii xs)
{- LINE 2 "quote_Eq.lhs" #-}
  quote_ ii (VEq_ a x y)  =  Inf_ (Eq_ (quote_ ii a) (quote_ ii x) (quote_ ii y))
  quote_ ii (VRefl_ a x)  =  Refl_ (quote_ ii a) (quote_ ii x)
{- LINE 2 "quote_Fin.lhs" #-}
  quote_ ii (VFin_ n)           =  Inf_ (Fin_ (quote_ ii n))
  quote_ ii (VFZero_ n)         =  FZero_ (quote_ ii n)
  quote_ ii (VFSucc_ n f)       =  FSucc_  (quote_ ii n) (quote_ ii f)
{- LINE 1735 "LP.lhs" #-}
  neutralQuote_ :: Int -> Neutral_ -> ITerm_
  neutralQuote_ ii (NFree_ v)
     =  boundfree_ ii v
  neutralQuote_ ii (NApp_ n v)
     =  neutralQuote_ ii n :$: quote_ ii v
{- LINE 2 "neutralQuote_Nat.lhs" #-}
  neutralQuote_ ii (NNatElim_ m z s n)
     =  NatElim_ (quote_ ii m) (quote_ ii z) (quote_ ii s) (Inf_ (neutralQuote_ ii n))
{- LINE 2 "neutralQuote_Vec.lhs" #-}
  neutralQuote_ ii (NVecElim_ a m mn mc n xs)
     =  VecElim_ (quote_ ii a) (quote_ ii m)
                 (quote_ ii mn) (quote_ ii mc)
                 (quote_ ii n) (Inf_ (neutralQuote_ ii xs))
{- LINE 2 "neutralQuote_Eq.lhs" #-}
  neutralQuote_ ii (NEqElim_ a m mr x y eq)
     =  EqElim_  (quote_ ii a) (quote_ ii m) (quote_ ii mr)
                 (quote_ ii x) (quote_ ii y)
                 (Inf_ (neutralQuote_ ii eq))
{- LINE 2 "neutralQuote_Fin.lhs" #-}
  neutralQuote_ ii (NFinElim_ m mz ms n f)
     =  FinElim_ (quote_ ii m)
                 (quote_ ii mz) (quote_ ii ms)
                 (quote_ ii n) (Inf_ (neutralQuote_ ii f))
{- LINE 1746 "LP.lhs" #-}
  boundfree_ :: Int -> Name -> ITerm_
  boundfree_ ii (Quote k vn)  =  Bound_ ((ii - k - 1) `max` 0) vn
  boundfree_ ii x             =  Free_ x
{- LINE 1751 "LP.lhs" #-}
  instance Show Value_ where
    show = show . quote0_
 
{- LINE 1775 "LP.lhs" #-}
  type Type_     =  Value_  
  type Context_    =  [(Name, Type_)]
{- LINE 1818 "LP.lhs" #-}
  quote0_ :: Value_ -> CTerm_
  quote0_ = quote_ 0 
 
  iType0_ :: (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
  iType0_ = iType_ 0
{- LINE 1826 "LP.lhs" #-}
  iType_ :: Int -> (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
  iType_ ii g (Ann_ e tyt )
    =     do  cType_  ii g tyt VStar_
              let ty = cEval_ tyt (fst g, [])  
              cType_ ii g e ty
              return ty
  iType_ ii g Star_   
     =  return VStar_   
  iType_ ii g (Pi_ vn tyt tyt')  
     =  do  cType_ ii g tyt VStar_    
            let ty = cEval_ tyt (fst g, [])  
            cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii vn, ty) : g))) g)  
                      (cSubst_ 0 (Free_ (Local ii vn)) tyt') VStar_  
            return VStar_   
  iType_ ii g (Free_ x)
    =     case lookup x (snd g) of
            Just ty        ->  return ty
            Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint_ 0 0 (Free_ x)))
  iType_ ii g (e1 :$: e2)
    =     do  si <- iType_ ii g e1
              case si of
                VPi_ _ ty ty'  ->  do  cType_ ii g e2 ty
                                       return ( ty' (cEval_ e2 (fst g, [])))
                _                  ->  throwError "illegal application"
{- LINE 2 "iType_Nat.lhs" #-}
  iType_ ii g Nat_                  =  return VStar_
  iType_ ii g (NatElim_ m mz ms n)  =
    do  cType_ ii g m (VPi_ "pix" VNat_ (const VStar_))
        let mVal  = cEval_ m (fst g, []) 
        cType_ ii g mz (mVal `vapp_` VZero_)
        cType_ ii g ms (VPi_ "piy" VNat_ (\ k -> VPi_ "piz" (mVal `vapp_` k) (\ _ -> mVal `vapp_` VSucc_ k)))
        cType_ ii g n VNat_
        let nVal = cEval_ n (fst g, [])
        return (mVal `vapp_` nVal)
{- LINE 2 "iType_Vec.lhs" #-}
  iType_ ii g (Vec_ a n) =
    do  cType_ ii g a  VStar_
        cType_ ii g n  VNat_
        return VStar_
  iType_ ii g (VecElim_ a m mn mc n vs) =
    do  cType_ ii g a VStar_
        let aVal = cEval_ a (fst g, [])
        cType_ ii g m
          (  VPi_ "" VNat_ (\n -> VPi_ "" (VVec_ aVal n) (\ _ -> VStar_)))
        let mVal = cEval_ m (fst g, [])
        cType_ ii g mn (foldl vapp_ mVal [VZero_, VNil_ aVal])
        cType_ ii g mc
          (  VPi_ "" VNat_ (\ n -> 
             VPi_ "" aVal (\ y -> 
             VPi_ "" (VVec_ aVal n) (\ ys ->
             VPi_ "" (foldl vapp_ mVal [n, ys]) (\ _ ->
             (foldl vapp_ mVal [VSucc_ n, VCons_ aVal n y ys]))))))
        cType_ ii g n VNat_
        let nVal = cEval_ n (fst g, [])
        cType_ ii g vs (VVec_ aVal nVal)
        let vsVal = cEval_ vs (fst g, [])
        return (foldl vapp_ mVal [nVal, vsVal])
{- LINE 2 "iType_Eq.lhs" #-}
  iType_ i g (Eq_ a x y) =
    do  cType_ i g a VStar_
        let aVal = cEval_ a (fst g, [])
        cType_ i g x aVal
        cType_ i g y aVal
        return VStar_
  iType_ i g (EqElim_ a m mr x y eq) =
    do  cType_ i g a VStar_
        let aVal = cEval_ a (fst g, [])
        cType_ i g m
          (VPi_ "" aVal (\ x ->
           VPi_ ""aVal (\ y ->
           VPi_ ""(VEq_ aVal x y) (\ _ -> VStar_)))) 
        let mVal = cEval_ m (fst g, [])
        cType_ i g mr
          (VPi_ "" aVal (\ x ->
           foldl vapp_ mVal [x, x]))
        cType_ i g x aVal
        let xVal = cEval_ x (fst g, [])
        cType_ i g y aVal
        let yVal = cEval_ y (fst g, [])
        cType_ i g eq (VEq_ aVal xVal yVal)
        let eqVal = cEval_ eq (fst g, [])
        return (foldl vapp_ mVal [xVal, yVal])
{- LINE 1857 "LP.lhs" #-}
  
{- LINE 1860 "LP.lhs" #-}
  cType_ :: Int -> (NameEnv Value_,Context_) -> CTerm_ -> Type_ -> Result ()
  cType_ ii g (Inf_ e) v 
    =     do  v' <- iType_ ii g e
              unless ( quote0_ v == quote0_ v') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint_ 0 0 (quote0_ v')) ++ "\n" ++ "type expected:  " ++ render (cPrint_ 0 0 (quote0_ v)) ++ "\n" ++ "for expression: " ++ render (iPrint_ 0 0 e)))
  cType_ ii g (Lam_ vn e) ( VPi_ vnt ty ty')
    =     cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii vn, ty ) : g))) g)
                  (cSubst_ 0 (Free_ (Local ii vn)) e) ( ty' (vfree_ (Local ii vn))) 
   --PROBLEM: one of these is vnt?
{- LINE 2 "cType_Nat.lhs" #-}
  cType_ ii g Zero_      VNat_  =  return ()
  cType_ ii g (Succ_ k)  VNat_  =  cType_ ii g k VNat_
{- LINE 2 "cType_Vec.lhs" #-}
  cType_ ii g (Nil_ a) (VVec_ bVal VZero_) =
    do  cType_ ii g a VStar_
        let aVal = cEval_ a (fst g, []) 
        unless  (quote0_ aVal == quote0_ bVal) 
                (throwError "type mismatch")
  cType_ ii g (Cons_ a n x xs) (VVec_ bVal (VSucc_ k)) =
    do  cType_ ii g a VStar_
        let aVal = cEval_ a (fst g, [])
        unless  (quote0_ aVal == quote0_ bVal)
                (throwError "type mismatch")
        cType_ ii g n VNat_
        let nVal = cEval_ n (fst g, [])
        unless  (quote0_ nVal == quote0_ k)
                (throwError "number mismatch")
        cType_ ii g x aVal
        cType_ ii g xs (VVec_ bVal k)
{- LINE 2 "cType_Eq.lhs" #-}
  cType_ ii g (Refl_ a z) (VEq_ bVal xVal yVal) =
    do  cType_ ii g a VStar_
        let aVal = cEval_ a (fst g, [])
        unless  (quote0_ aVal == quote0_ bVal)
                (throwError "type mismatch")
        cType_ ii g z aVal
        let zVal = cEval_ z (fst g, [])
        unless  (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
                (throwError "type mismatch")
{- LINE 1873 "LP.lhs" #-}
  cType_ ii g _ _
    =     throwError "type mismatch"
{- LINE 1992 "LP.lhs" #-}
  data Nat = Zero | Succ Nat
{- LINE 2004 "LP.lhs" #-}
  plus :: Nat -> Nat -> Nat 
  plus Zero n      = n 
  plus (Succ k) n  = Succ (plus k n) 

