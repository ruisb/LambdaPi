module LambdaPi.Functions where
import Interpreter.Types
import LambdaPi.Types
import LambdaPi.Printer

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ hiding (parens)

vapp :: Value -> Value -> Value
vapp x v = case x of
  VLam _ f   -> f v
  VNeutral n -> VNeutral $ NApp n v

-- Creates the value corresponding to a free variable.
vfree :: Name -> Value
vfree n = VNeutral $ NFree n

vquote = VNeutral . NQuote 

-- Evaluate a checkable term.
cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval x d = case x of
  Inf  ii       -> iEval ii d
  Lam vn c      -> VLam vn (\ x -> cEval c (((\(e, d) -> (e,  (x : d))) d)))
  Zero          -> VZero
  Succ k        -> VSucc  (cEval k d)
  Nil a         -> VNil   (cEval a d)
  Cons a n x xs -> VCons  (cEval a d) (cEval n d) (cEval x d) (cEval xs d)
  Refl a x      -> VRefl  (cEval a d) (cEval x d)
  FZero n       -> VFZero (cEval n d)
  FSucc n f     -> VFSucc (cEval n d) (cEval f d)

-- Evaluate an inferable term.
iEval :: ITerm -> (NameEnv Value, Env) -> Value
iEval x d = case x of
  Ann  c _                   -> cEval c d
  Star                       -> VStar   
  Pi vn ty ty'               -> VPi vn (cEval ty d) (\ x -> 
                                    cEval ty' (((\(e, d) -> (e,  (x : d))) d)))
  Free   x                   -> case lookup x (fst d) of 
                                    Nothing ->  (vfree x)
                                    Just v -> v 
  Bound  ii                  -> (snd d) !! ii
  i :$: c                    -> vapp (iEval i d) (cEval c d)
  Nat                        -> VNat
  NatElim m mz ms n          -> rec (cEval n d)
    where
      mzVal            = cEval mz d
      msVal            = cEval ms d
      rec VZero        = mzVal
      rec (VSucc k)    = msVal `vapp` k `vapp` rec k
      rec (VNeutral n) = VNeutral (NNatElim (cEval m d) mzVal msVal n)
      rec _            = error "internal: eval natElim"
  Vec  a n                   -> VVec (cEval a d) (cEval n d)
  VecElim a m mn mc n xs     -> rec (cEval n d) (cEval xs d)
    where
      mnVal = cEval mn d
      mcVal = cEval mc d
      rec nVal (VNil  _)         = mnVal
      rec nVal (VCons  k x xs _) = foldl vapp mcVal [k, x, xs, rec k xs]
      rec nVal (VNeutral n)      = VNeutral $ NVecElim  (cEval a d) (cEval m d)
                                                         mnVal mcVal nVal n
      rec _ _                    =  error "internal: eval vecElim"
  Eq a  x y                   -> VEq (cEval a d) (cEval x d) (cEval y d)
  EqElim a m mr x y eq        -> rec (cEval eq d)
    where
      mrVal = cEval mr d
      rec (VRefl _  z) = mrVal `vapp` z
      rec (VNeutral n) = VNeutral (NEqElim  (cEval a d) (cEval m d) mrVal
                                            (cEval x d) (cEval y d) n)
      rec _            = error "internal: eval eqElim"
  Fin  n                     -> VFin (cEval n d)
  FinElim m mz ms n f        -> rec (cEval f d)
    where
      mzVal = cEval mz d
      msVal = cEval ms d
      rec (VFZero k)    = mzVal `vapp` k
      rec (VFSucc k g)  = foldl vapp msVal [k, g, rec g]
      rec (VNeutral n') = VNeutral $ NFinElim  (cEval m d) (cEval mz d)
                                     (cEval ms d) (cEval n d) n'
      rec  _            = error "internal: eval finElim"

-- Subsitute an inferable term with another inferable term.
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c')     = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii r  Star           = Star  
iSubst ii r  (Pi vn ty ty') = Pi vn (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j)      = if ii == j then i' else Bound j
iSubst ii i' (Free y)       = Free y
iSubst ii i' (i :$: c)      = iSubst ii i' i :$: cSubst ii i' c
iSubst ii r  Nat            = Nat
iSubst ii r  (NatElim m mz ms n)
  = NatElim (cSubst ii r m)
            (cSubst ii r mz) (cSubst ii r ms)
            (cSubst ii r ms)
iSubst ii r  (Vec a n)      = Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r  (VecElim a m mn mc n xs)
  = VecElim (cSubst ii r a) (cSubst ii r m)
            (cSubst ii r mn) (cSubst ii r mc)
            (cSubst ii r n) (cSubst ii r xs)
iSubst ii r  (Eq a x y)     = Eq (cSubst ii r a)
                                 (cSubst ii r x) (cSubst ii r y)
iSubst ii r  (EqElim a m mr x y eq)
  = VecElim (cSubst ii r a) (cSubst ii r m)
            (cSubst ii r mr) (cSubst ii r x)
            (cSubst ii r y) (cSubst ii r eq)
iSubst ii r  (Fin n)       = Fin (cSubst ii r n)
iSubst ii r  (FinElim m mz ms n f)
  = FinElim (cSubst ii r m)
            (cSubst ii r mz) (cSubst ii r ms)
            (cSubst ii r n) (cSubst ii r f)

-- Subsitute an inferable term with a checkable term.
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)     = Inf (iSubst ii i' i)
cSubst ii i' (Lam vn c)  = Lam vn (cSubst (ii + 1) i' c)
-- PROBLEM:CAPTURE?

cSubst ii r  Zero        = Zero
cSubst ii r  (Succ n)    = Succ (cSubst ii r n)
cSubst ii r  (Nil a)     = Nil (cSubst ii r a)
cSubst ii r  (Cons a n x xs)
  = Cons (cSubst ii r a) (cSubst ii r x)
         (cSubst ii r x) (cSubst ii r xs)
cSubst ii r  (Refl a x)  = Refl (cSubst ii r a) (cSubst ii r x)
cSubst ii r  (FZero n)   = FZero (cSubst ii r n)
cSubst ii r  (FSucc n k) = FSucc (cSubst ii r n) (cSubst ii r k)

-- Make a value printable.
-- REMARK: really needed for printing functions.
quote :: Int -- counts the number of binders we have traversed
         -> Value -> CTerm
quote ii x = case x of
  VLam vn t      -> Lam vn (quote (ii + 1) (t (vquote ii)))
  VStar          -> Inf Star 
  VPi vn v f     -> Inf (Pi vn (quote ii v) (quote (ii + 1)
                               (f (vquote ii))))
  VNeutral n     -> Inf (neutralQuote ii n)
  VNat           -> Inf Nat
  VZero          -> Zero
  VSucc n        -> Succ (quote ii n)
  VVec a n       -> Inf (Vec (quote ii a) (quote ii n))
  VNil a         -> Nil (quote ii a)
  VCons a n x xs -> Cons (quote ii a) (quote ii n)
                         (quote ii x) (quote ii xs)
  VEq a x y      -> Inf (Eq (quote ii a) (quote ii x) (quote ii y))
  VRefl a x      -> Refl (quote ii a) (quote ii x)
  VFin n         -> Inf (Fin (quote ii n))
  VFZero n       -> FZero (quote ii n)
  VFSucc n f     -> FSucc  (quote ii n) (quote ii f)
  where
  -- Quote the arguments.
  neutralQuote :: Int -> Neutral -> ITerm
  neutralQuote ii x = case x of
    NFree v  -> Free v
    NQuote k -> Bound ((ii - k -1) `max` 0)
    NApp n v -> neutralQuote ii n :$: quote ii v
    NNatElim m z s n
      -> NatElim (quote ii m) (quote ii z) (quote ii s)
                 (Inf (neutralQuote ii n))
    NVecElim a m mn mc n xs
      -> VecElim (quote ii a) (quote ii m)
                (quote ii mn) (quote ii mc)
                (quote ii n) (Inf (neutralQuote ii xs))
    NEqElim a m mr x y eq
      -> EqElim  (quote ii a) (quote ii m) (quote ii mr)
                (quote ii x) (quote ii y)
                (Inf (neutralQuote ii eq))
    NFinElim m mz ms n f
      -> FinElim (quote ii m)
                (quote ii mz) (quote ii ms)
                (quote ii n) (Inf (neutralQuote ii f))
  
-- A value can be printed when it first is quoted.
instance Show Value where
  show = show . quote0

type Type    = Value  
-- Associate names with types.
type Context = [(Name, Type)]

quote0 :: Value -> CTerm
quote0 = quote 0 

-- Type check an inferable term.
iType :: (NameEnv Value, Context) -> ITerm -> Result Type
iType g (Ann e tyt )
  = do cType  g tyt VStar
       let ty = cEval tyt (fst g, [])  
       cType g e ty
       return ty
iType g Star = return VStar   
iType g (Pi vn tyt tyt')  
  = do cType g tyt VStar    
       let ty = cEval tyt (fst g, [])  
       cType  ((\ (d,g) -> (d,  (vn, ty) : g)) g)
              (cSubst 0 (Free vn) tyt') VStar
       return VStar   
iType g (Free x)
  = case lookup x (snd g) of
        Just ty ->  return ty
        Nothing ->  throwError ("unknown identifier: " 
                                ++ render (iPrint (Free x)))
iType g (e1 :$: e2)
  = do  si <- iType g e1
        case si of
          VPi _ ty ty' -> do cType g e2 ty
                             return ( ty' (cEval e2 (fst g, [])))
          _            ->  throwError "illegal application"

iType g Nat                  = return VStar
iType g (NatElim m mz ms n)
  = do cType g m (VPi "pix" VNat (const VStar))
       let mVal = cEval m (fst g, []) 
       cType g mz (mVal `vapp` VZero)
       cType g ms (VPi "piy" VNat (\ k -> VPi "piz" (mVal `vapp` k) 
                                     (\_ -> mVal `vapp` VSucc k)))
       cType g n VNat
       let nVal = cEval n (fst g, [])
       return (mVal `vapp` nVal)
iType g (Vec a n)
  = do cType g a  VStar
       cType g n  VNat
       return VStar
iType g (VecElim a m mn mc n vs)
  = do cType g a VStar
       let aVal = cEval a (fst g, [])
       cType g m
             (VPi "" VNat (\n -> VPi "" (VVec aVal n) (\_ -> VStar)))
       let mVal = cEval m (fst g, [])
       cType g mn (foldl vapp mVal [VZero, VNil aVal])
       cType g mc
         (VPi "" VNat (\ n -> 
          VPi "" aVal (\ y -> 
          VPi "" (VVec aVal n) (\ ys ->
          VPi "" (foldl vapp mVal [n, ys]) (\_ ->
          (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
       cType g n VNat
       let nVal = cEval n (fst g, [])
       cType g vs (VVec aVal nVal)
       let vsVal = cEval vs (fst g, [])
       return (foldl vapp mVal [nVal, vsVal])
iType g (Eq a x y)
  = do cType g a VStar
       let aVal = cEval a (fst g, [])
       cType g x aVal
       cType g y aVal
       return VStar
iType g (EqElim a m mr x y eq)
  = do cType g a VStar
       let aVal = cEval a (fst g, [])
       cType g m
         (VPi "" aVal (\ x ->
          VPi ""aVal (\ y ->
          VPi ""(VEq aVal x y) (\_ -> VStar)))) 
       let mVal = cEval m (fst g, [])
       cType g mr
         (VPi "" aVal (\ x ->
          foldl vapp mVal [x, x]))
       cType g x aVal
       let xVal = cEval x (fst g, [])
       cType g y aVal
       let yVal = cEval y (fst g, [])
       cType g eq (VEq aVal xVal yVal)
       let eqVal = cEval eq (fst g, [])
       return (foldl vapp mVal [xVal, yVal])

-- Type check a checkable term.
cType :: (NameEnv Value, Context) -> CTerm -> Type -> Result ()
cType g (Inf e) v 
  = do v' <- iType g e
       unless ( quote0 v == quote0 v') (throwError ("type mismatch:\n"
                                        ++ "type inferred:  "
                                        ++ render (cPrint (quote0 v'))
                                        ++ "\n" ++ "type expected:  "
                                        ++ render (cPrint (quote0 v))
                                        ++ "\n" ++ "for expression: " 
                                        ++ render (iPrint e)))
cType g (Lam vn e) ( VPi vnt ty ty')
  =    cType  ((\(d, g) -> (d, (vn, ty) : g)) g)
              (cSubst 0 (Free vn) e) (ty' (vfree vn))
-- FIXME PROBLEM: one of these is vnt?
-- FIXME boilerplate code?
cType g Zero      VNat              = return ()
cType g (Succ k)  VNat              = cType g k VNat
cType g (Nil a)   (VVec bVal VZero)
  = do  cType g a VStar
        let aVal = cEval a (fst g, []) 
        unless  (quote0 aVal == quote0 bVal) 
                (throwError "type mismatch")
cType g (Cons a n x xs) (VVec bVal (VSucc k))
  = do  cType g a VStar
        let aVal = cEval a (fst g, [])
        unless  (quote0 aVal == quote0 bVal)
                (throwError "type mismatch")
        cType g n VNat
        let nVal = cEval n (fst g, [])
        unless  (quote0 nVal == quote0 k)
                (throwError "number mismatch")
        cType g x aVal
        cType g xs (VVec bVal k)
cType g (Refl a z) (VEq bVal xVal yVal)
  = do  cType g a VStar
        let aVal = cEval a (fst g, [])
        unless  (quote0 aVal == quote0 bVal)
                (throwError "type mismatch")
        cType g z aVal
        let zVal = cEval z (fst g, [])
        unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
                (throwError "type mismatch")
cType g _ _
  = throwError "type mismatch"
