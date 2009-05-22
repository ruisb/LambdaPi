module LambdaPi.Functions where
import Interpreter.Types
import LambdaPi.Types
import LambdaPi.Printer

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ hiding (parens)

vapp :: Value -> Value -> Value
vapp (VLam _ f)    v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval (Inf  ii)        d = iEval ii d
cEval (Lam vn c)       d = VLam vn (\ x -> 
                               cEval c (((\(e, d) -> (e,  (x : d))) d)))
cEval Zero             d = VZero
cEval (Succ k)         d = VSucc (cEval k d)
cEval (Nil a)          d = VNil  (cEval a d)
cEval (Cons a n x xs)  d = VCons (cEval a d) (cEval n d)
                                    (cEval x d) (cEval xs d)
cEval (Refl a x)       d = VRefl (cEval a d) (cEval x d)
cEval (FZero n)        d = VFZero (cEval n d)
cEval (FSucc n f)      d = VFSucc (cEval n d) (cEval f d)

iEval :: ITerm -> (NameEnv Value,Env) -> Value
iEval (Ann c _)        d  =  cEval c d
iEval Star             d  =  VStar   
iEval (Pi vn ty ty')   d  =  VPi vn (cEval ty d) (\ x -> 
                                 cEval ty' (((\(e, d) -> (e,  (x : d))) d)))
iEval (Free  x)        d  =  case lookup x (fst d) of 
                                 Nothing ->  (vfree x)
                                 Just v -> v 
iEval (Bound  ii _)      d  =  (snd d) !! ii
iEval (i :$: c)         d  =  vapp (iEval i d) (cEval c d)
iEval Nat                  d  =  VNat
iEval (NatElim m mz ms n)  d 
  =  let  mzVal = cEval mz d
          msVal = cEval ms d
          rec nVal =
            case nVal of
              VZero       ->  mzVal
              VSucc k     ->  msVal `vapp` k `vapp` rec k
              VNeutral n  ->  VNeutral
                               (NNatElim (cEval m d) mzVal msVal n)
              _           ->  error "internal: eval natElim"
     in   rec (cEval n d)
iEval (Vec a n)                 d  =  VVec (cEval a d) (cEval n d)
iEval (VecElim a m mn mc n xs)  d  =
  let  mnVal  =  cEval mn d
       mcVal  =  cEval mc d
       rec nVal xsVal =
         case xsVal of
           VNil  _          ->  mnVal
           VCons  k x xs _  ->  foldl vapp mcVal [k, x, xs, rec k xs]
           VNeutral n       ->  VNeutral
                                (NVecElim  (cEval a d) (cEval m d)
                                            mnVal mcVal nVal n)
           _              ->  error "internal: eval vecElim"
  in   rec (cEval n d) (cEval xs d)
iEval (Eq a x y)                d  =  VEq (cEval a d) (cEval x d) (cEval y d)
iEval (EqElim a m mr x y eq)    d  =
  let  mrVal  =  cEval mr d
       rec eqVal =
         case eqVal of
           VRefl _ z -> mrVal `vapp` z
           VNeutral n ->  
             VNeutral (NEqElim  (cEval a d) (cEval m d) mrVal
                                  (cEval x d) (cEval y d) n)
           _ -> error "internal: eval eqElim"
  in   rec (cEval eq d)
iEval (Fin n)                d  =  VFin (cEval n d)
iEval (FinElim m mz ms n f)  d  =
  let  mzVal  =  cEval mz d
       msVal  =  cEval ms d
       rec fVal =
         case fVal of
           VFZero k        ->  mzVal `vapp` k
           VFSucc k g      ->  foldl vapp msVal [k, g, rec g]
           VNeutral n'     ->  VNeutral
                                (NFinElim  (cEval m d) (cEval mz d)
                                            (cEval ms d) (cEval n d) n')
           _               ->  error "internal: eval finElim"
  in   rec (cEval f d)

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i'   (Ann c c')     =  Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii r  Star           =  Star  
iSubst ii r  (Pi vn ty ty') =  Pi vn (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j vn)   =  if ii == j then i' else Bound j vn
iSubst ii i' (Free y)       =  Free y
iSubst ii i' (i :$: c)       =  iSubst ii i' i :$: cSubst ii i' c
iSubst ii r  Nat            =  Nat
iSubst ii r  (NatElim m mz ms n)
                              =  NatElim (cSubst ii r m)
                                          (cSubst ii r mz) (cSubst ii r ms)
                                          (cSubst ii r ms)
iSubst ii r  (Vec a n)      =  Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r  (VecElim a m mn mc n xs)
                              =  VecElim (cSubst ii r a) (cSubst ii r m)
                                          (cSubst ii r mn) (cSubst ii r mc)
                                          (cSubst ii r n) (cSubst ii r xs)
iSubst ii r  (Eq a x y)     =  Eq (cSubst ii r a)
                                     (cSubst ii r x) (cSubst ii r y)
iSubst ii r  (EqElim a m mr x y eq)
                              =  VecElim (cSubst ii r a) (cSubst ii r m)
                                          (cSubst ii r mr) (cSubst ii r x)
                                          (cSubst ii r y) (cSubst ii r eq)
iSubst ii r  (Fin n)        =  Fin (cSubst ii r n)
iSubst ii r  (FinElim m mz ms n f)
                              =  FinElim (cSubst ii r m)
                                          (cSubst ii r mz) (cSubst ii r ms)
                                          (cSubst ii r n) (cSubst ii r f)
                                          
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)      =  Inf (iSubst ii i' i)
cSubst ii i' (Lam vn c)   =  Lam vn (cSubst (ii + 1) i' c)
-- PROBLEM:CAPTURE?

cSubst ii r  Zero         =  Zero
cSubst ii r  (Succ n)     =  Succ (cSubst ii r n)
cSubst ii r  (Nil a)      =  Nil (cSubst ii r a)
cSubst ii r  (Cons a n x xs)
                            =  Cons (cSubst ii r a) (cSubst ii r x)
                                     (cSubst ii r x) (cSubst ii r xs)
cSubst ii r  (Refl a x)   =  Refl (cSubst ii r a) (cSubst ii r x)
cSubst ii r  (FZero n)    =  FZero (cSubst ii r n)
cSubst ii r  (FSucc n k)  =  FSucc (cSubst ii r n) (cSubst ii r k)

quote :: Int -> Value -> CTerm
quote ii (VLam vn t)
  =     Lam vn (quote (ii + 1) (t (vfree (Quote ii vn))))
quote ii VStar = Inf Star 
quote ii (VPi vn v f)                                       
    =  Inf (Pi vn (quote ii v) (quote (ii + 1) (f (vfree (Quote ii vn )))))  
quote ii (VNeutral n)
  =     Inf (neutralQuote ii n)
quote ii VNat       =  Inf Nat
quote ii VZero      =  Zero
quote ii (VSucc n)  =  Succ (quote ii n)
quote ii (VVec a n)         =  Inf (Vec (quote ii a) (quote ii n))
quote ii (VNil a)           =  Nil (quote ii a)
quote ii (VCons a n x xs)   =  Cons  (quote ii a) (quote ii n)
                                        (quote ii x) (quote ii xs)
quote ii (VEq a x y)  =  Inf (Eq (quote ii a) (quote ii x) (quote ii y))
quote ii (VRefl a x)  =  Refl (quote ii a) (quote ii x)
quote ii (VFin n)           =  Inf (Fin (quote ii n))
quote ii (VFZero n)         =  FZero (quote ii n)
quote ii (VFSucc n f)       =  FSucc  (quote ii n) (quote ii f)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v)
   =  boundfree ii v
neutralQuote ii (NApp n v)
   =  neutralQuote ii n :$: quote ii v
neutralQuote ii (NNatElim m z s n)
   =  NatElim (quote ii m) (quote ii z) (quote ii s) (Inf (neutralQuote ii n))
neutralQuote ii (NVecElim a m mn mc n xs)
   =  VecElim (quote ii a) (quote ii m)
               (quote ii mn) (quote ii mc)
               (quote ii n) (Inf (neutralQuote ii xs))
neutralQuote ii (NEqElim a m mr x y eq)
   =  EqElim  (quote ii a) (quote ii m) (quote ii mr)
               (quote ii x) (quote ii y)
               (Inf (neutralQuote ii eq))
neutralQuote ii (NFinElim m mz ms n f)
   =  FinElim (quote ii m)
               (quote ii mz) (quote ii ms)
               (quote ii n) (Inf (neutralQuote ii f))

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k vn)  =  Bound ((ii - k - 1) `max` 0) vn
boundfree ii x             =  Free x

instance Show Value where
  show = show . quote0


type Type     =  Value  
type Context    =  [(Name, Type)]

quote0 :: Value -> CTerm
quote0 = quote 0 

iType0 :: (NameEnv Value,Context) -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> (NameEnv Value,Context) -> ITerm -> Result Type
iType ii g (Ann e tyt )
  =     do  cType  ii g tyt VStar
            let ty = cEval tyt (fst g, [])  
            cType ii g e ty
            return ty
iType ii g Star   
   =  return VStar   
iType ii g (Pi vn tyt tyt')  
   =  do  cType ii g tyt VStar    
          let ty = cEval tyt (fst g, [])  
          cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii vn, ty) : g))) g)  
                    (cSubst 0 (Free (Local ii vn)) tyt') VStar  
          return VStar   
iType ii g (Free x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint 0 0 (Free x)))
iType ii g (e1 :$: e2)
  =     do  si <- iType ii g e1
            case si of
              VPi _ ty ty'  ->  do  cType ii g e2 ty
                                    return ( ty' (cEval e2 (fst g, [])))
              _                ->  throwError "illegal application"

iType ii g Nat                  =  return VStar
iType ii g (NatElim m mz ms n)  =
  do  cType ii g m (VPi "pix" VNat (const VStar))
      let mVal  = cEval m (fst g, []) 
      cType ii g mz (mVal `vapp` VZero)
      cType ii g ms (VPi "piy" VNat (\ k -> VPi "piz" (mVal `vapp` k) (\_ -> mVal `vapp` VSucc k)))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      return (mVal `vapp` nVal)
iType ii g (Vec a n) =
  do  cType ii g a  VStar
      cType ii g n  VNat
      return VStar
iType ii g (VecElim a m mn mc n vs) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      cType ii g m
        (  VPi "" VNat (\n -> VPi "" (VVec aVal n) (\_ -> VStar)))
      let mVal = cEval m (fst g, [])
      cType ii g mn (foldl vapp mVal [VZero, VNil aVal])
      cType ii g mc
        (  VPi "" VNat (\ n -> 
           VPi "" aVal (\ y -> 
           VPi "" (VVec aVal n) (\ ys ->
           VPi "" (foldl vapp mVal [n, ys]) (\_ ->
           (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      cType ii g vs (VVec aVal nVal)
      let vsVal = cEval vs (fst g, [])
      return (foldl vapp mVal [nVal, vsVal])
iType i g (Eq a x y) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g x aVal
      cType i g y aVal
      return VStar
iType i g (EqElim a m mr x y eq) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g m
        (VPi "" aVal (\ x ->
         VPi ""aVal (\ y ->
         VPi ""(VEq aVal x y) (\_ -> VStar)))) 
      let mVal = cEval m (fst g, [])
      cType i g mr
        (VPi "" aVal (\ x ->
         foldl vapp mVal [x, x]))
      cType i g x aVal
      let xVal = cEval x (fst g, [])
      cType i g y aVal
      let yVal = cEval y (fst g, [])
      cType i g eq (VEq aVal xVal yVal)
      let eqVal = cEval eq (fst g, [])
      return (foldl vapp mVal [xVal, yVal])



cType :: Int -> (NameEnv Value,Context) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v 
  =     do  v' <- iType ii g e
            unless ( quote0 v == quote0 v') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint 0 0 (quote0 v')) ++ "\n" ++ "type expected:  " ++ render (cPrint 0 0 (quote0 v)) ++ "\n" ++ "for expression: " ++ render (iPrint 0 0 e)))
cType ii g (Lam vn e) ( VPi vnt ty ty')
  =     cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii vn, ty ) : g))) g)
                (cSubst 0 (Free (Local ii vn)) e) ( ty' (vfree (Local ii vn))) 
 --PROBLEM: one of these is vnt?

cType ii g Zero      VNat  =  return ()
cType ii g (Succ k)  VNat  =  cType ii g k VNat
cType ii g (Nil a) (VVec bVal VZero) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, []) 
      unless  (quote0 aVal == quote0 bVal) 
              (throwError "type mismatch")
cType ii g (Cons a n x xs) (VVec bVal (VSucc k)) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      unless  (quote0 nVal == quote0 k)
              (throwError "number mismatch")
      cType ii g x aVal
      cType ii g xs (VVec bVal k)
cType ii g (Refl a z) (VEq bVal xVal yVal) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g z aVal
      let zVal = cEval z (fst g, [])
      unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
              (throwError "type mismatch")
cType ii g _ _
  =     throwError "type mismatch"

