module LambdaPi.Functions where
import Interpreter.Types
import LambdaPi.Types
import LambdaPi.Printer

import Data.Maybe
import Control.Monad.Error
import Control.Arrow
import Text.PrettyPrint.HughesPJ hiding (parens)


import Debug.Trace


vapp :: Value -> Value -> Value
vapp (VLam _ f)   v = f v
vapp (VNeutral n) v = VNeutral $ NApp n v
vapp x y = error$ "non exhausive : vapp "++show x ++ show y

-- Creates the value corresponding to a free variable.
vfree  :: Name -> Value
vfree  = VNeutral . NFree

vquote :: Int  -> Value
vquote = VNeutral . NQuote 

-- Evaluate a checkable term.
cEval :: CTerm -> (NameEnv Value, Env) -> Value
cEval x d@(ne, e) = case x of
  Inf  ii       -> iEval ii d
  Lam vn c      -> VLam vn (\x -> cEval c (ne, x:e))
--HERE  DataCons _ _  -> error "this evaluation (of a term data constructor) should not happen"
-----  DataCons cid args -> VDataCons cid (map (`cEval`d) args)
-----  -- for hardcoded datatypes
-----  Zero          -> VZero
-----  Succ k        -> VSucc  (cEval k d)
-----  Nil a         -> VNil   (cEval a d)
-----  Cons a n x xs -> VCons  (cEval a d) (cEval n d) (cEval x d) (cEval xs d)
-----  Refl a x      -> VRefl  (cEval a d) (cEval x d)
-----  FZero n       -> VFZero (cEval n d)
-----  FSucc n f     -> VFSucc (cEval n d) (cEval f d)


-- Evaluate an inferable term.
iEval :: ITerm -> (NameEnv Value, Env) -> Value
iEval x d@(ne, e) = case x of
  Ann  c _                   -> cEval c d
  Star                       -> VStar   
  Pi vn ty ty'               -> VPi vn (cEval ty d) (\x -> cEval ty' (ne, x:e))
  Free   x                   ->  case lookup x (fst d) of 
                                    Nothing ->(vfree x)
                                    Just v  ->  v 
  Bound  ii                  ->  e !! ii --(!!!!) ("ERROR when finding Bound "++show ii++ "in context "++show e) e ii
  i :$: c                    -> vapp (iEval i d) (cEval c d)
 --HERE  TypeCons did args          -> VTypeCons did (map (`cEval`d) args)
        --error "panic: this evaluation (of a term type constructor) should not happen" --
  DataElim dt mot met ts t   -> eliminate d dt (cEval mot d) (map (`cEval` d) met) (map (`cEval` d) ts) (cEval t d)  
--                           -> rec (map (`cEval` d) ts) (cEval t d)
--               where consTy cid    = fromJust . lookup cid . ctors $ dt
--                     mtsVal        = map (`cEval` d) met
--	             conMtsVal cid = fromJust . lookup cid . zip (map fst (ctors dt)) $ mtsVal
--                     rec tsVals (VDataCons cid args) = let ctyargs = fst . vunprefix . (`cEval` d) . consTy $ cid
--		                                           chirec  = map ((==infFree (name dt)).quote0.fst.vunapps.snd) ctyargs
--                                                           indargs = (map snd . filter fst) (zip chirec args)
--		                                       in  (conMtsVal cid) `vapps` args `vapps` map (rec tsVals) indargs
--		     rec tsVals (VNeutral n) = VNeutral $ NDataElim dt (cEval mot d) mtsVal tsVals n
--		     rec _      _            = error "panic: bad input to eval of an eliminator"

eliminate :: (NameEnv Value, Env) -- just needed to evaluate the constructor types and get which are recursive arguments. it can be the env at definition of the data type.
          -> DataInfo CTerm -> Value -> [Value] -> [Value] -> Value -> Value
eliminate d dt mot met ts t   = rec ts t
       where consTy cid    = fromJust . lookup cid . ctors $ dt
             conMtsVal cid = fromJust . lookup cid . zip (map fst (ctors dt)) $ met
             rec tsVals (VDataCons cid args) = let ctyargs = fst . vunprefixDummy . (`cEval` d) . consTy $ cid
	                                           chirec  = map (maybe False (==name dt).vmainty.snd) ctyargs
                                                   indargs = (map snd . filter fst) (zip chirec args)
	                                       in  (conMtsVal cid) `vapps` args `vapps` map (rec tsVals) indargs
	     rec tsVals (VNeutral n) = VNeutral $ NDataElim dt mot met tsVals n
	     rec _      _            = error "panic: bad input to eval of an eliminator"
--   where 
--      mtsVal = map (`cEval` d) mts
--      rec (VDataCons cid vargs) =     
--      rec parVal (VNeutral n)   = VNeutral$ NDataElim did (map (cEval d) par) (cEval mot d) mtsVal n
--      rec _                     =  error "internal: eval dataElim"
  ------
  -- for hardcoded datatypes
-----  Nat                        -> VNat
-----  NatElim m mz ms n          -> rec (cEval n d)
-----    where
-----      mzVal            = cEval mz d
-----      msVal            = cEval ms d
-----      rec VZero        = mzVal
-----      rec (VSucc k)    = msVal `vapp` k `vapp` rec k
-----      rec (VNeutral n) = VNeutral (NNatElim (cEval m d) mzVal msVal n)
-----      rec _            = error "internal: eval natElim"
-----  Vec  a n                   -> VVec (cEval a d) (cEval n d)
-----  VecElim a m mn mc n xs     -> rec (cEval n d) (cEval xs d)
-----    where
-----      mnVal = cEval mn d
-----      mcVal = cEval mc d
-----      rec nVal (VNil  _)         = mnVal
-----      rec nVal (VCons  k x xs _) = foldl vapp mcVal [k, x, xs, rec k xs]
-----      rec nVal (VNeutral n)      = VNeutral $ NVecElim  (cEval a d) (cEval m d)
-----                                                         mnVal mcVal nVal n
-----      rec _ _                    =  error "internal: eval vecElim"
-----  Eq a  x y                   -> VEq (cEval a d) (cEval x d) (cEval y d)
-----  EqElim a m mr x y eq        -> rec (cEval eq d)
-----    where
-----      mrVal = cEval mr d
-----      rec (VRefl _  z) = mrVal `vapp` z
-----      rec (VNeutral n) = VNeutral (NEqElim  (cEval a d) (cEval m d) mrVal
-----                                            (cEval x d) (cEval y d) n)
-----      rec _            = error "internal: eval eqElim"
-----  Fin  n                     -> VFin (cEval n d)
-----  FinElim m mz ms n f        -> rec (cEval f d)
-----    where
-----      mzVal = cEval mz d
-----      msVal = cEval ms d
-----      rec (VFZero k)    = mzVal `vapp` k
-----      rec (VFSucc k g)  = foldl vapp msVal [k, g, rec g]
-----      rec (VNeutral n') = VNeutral $ NFinElim  (cEval m d) (cEval mz d)
-----                                     (cEval ms d) (cEval n d) n'
-----      rec  _            = error "internal: eval finElim"
-----




-- Subsitute an inferable term with another inferable term.
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c')         = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii r  Star               = Star  
iSubst ii r  (Pi vn ty ty')     = Pi vn (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j)          = if ii == j then i' else Bound j
iSubst ii i' (Free y)           = Free y
iSubst ii i' (i :$: c)          = iSubst ii i' i :$: cSubst ii i' c
--HERE iSubst ii r  (TypeCons did args) = TypeCons did (map (cSubst ii r) args)
iSubst ii r  (DataElim did mot met ts t) = DataElim did (cSubst ii r mot) (map (cSubst ii r) met) (map (cSubst ii r) ts) (cSubst ii r t) 
-- for hardcoded datatypes
-----iSubst ii r  Nat            = Nat
-----iSubst ii r  (NatElim m mz ms n)
-----  = NatElim (cSubst ii r m)
-----            (cSubst ii r mz) (cSubst ii r ms)
-----            (cSubst ii r ms)
-----iSubst ii r  (Vec a n)      = Vec (cSubst ii r a) (cSubst ii r n)
-----iSubst ii r  (VecElim a m mn mc n xs)
-----  = VecElim (cSubst ii r a) (cSubst ii r m)
-----            (cSubst ii r mn) (cSubst ii r mc)
-----            (cSubst ii r n) (cSubst ii r xs)
-----iSubst ii r  (Eq a x y)     = Eq (cSubst ii r a)
-----                                 (cSubst ii r x) (cSubst ii r y)
-----iSubst ii r  (EqElim a m mr x y eq)
-----  = VecElim (cSubst ii r a) (cSubst ii r m)
-----            (cSubst ii r mr) (cSubst ii r x)
-----            (cSubst ii r y) (cSubst ii r eq)
-----iSubst ii r  (Fin n)       = Fin (cSubst ii r n)
-----iSubst ii r  (FinElim m mz ms n f)
-----  = FinElim (cSubst ii r m)
-----            (cSubst ii r mz) (cSubst ii r ms)
-----            (cSubst ii r n) (cSubst ii r f)

-- Subsitute an inferable term with a checkable term.
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)     = Inf (iSubst ii i' i)
cSubst ii i' (Lam vn c)  = Lam vn (cSubst (ii + 1) i' c)-- PROBLEM:CAPTURE?
-- HERE: cSubst ii r (DataCons cid args) = DataCons cid (map (cSubst ii r) args)
------- for hardcoded datatypes
-----cSubst ii r  Zero        = Zero
-----cSubst ii r  (Succ n)    = Succ (cSubst ii r n)
-----cSubst ii r  (Nil a)     = Nil (cSubst ii r a)
-----cSubst ii r  (Cons a n x xs)
-----  = Cons (cSubst ii r a) (cSubst ii r x)
-----         (cSubst ii r x) (cSubst ii r xs)
-----cSubst ii r  (Refl a x)  = Refl (cSubst ii r a) (cSubst ii r x)
-----cSubst ii r  (FZero n)   = FZero (cSubst ii r n)
-----cSubst ii r  (FSucc n k) = FSucc (cSubst ii r n) (cSubst ii r k)

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
  VTypeCons did argVals  -> quote ii $ vfree did `vapps` argVals
  --HERE VTypeCons did argVals  -> Inf$ TypeCons did (map (quote ii) argVals)
  VDataCons cid argVals -> quote ii $ vfree cid `vapps` argVals 
  --HERE VDataCons cid argVals -> DataCons cid (map (quote ii) argVals)
-----  -- for hardcoded datatypes
-----  VNat           -> Inf Nat
-----  VZero          -> Zero
-----  VSucc n        -> Succ (quote ii n)
-----  VVec a n       -> Inf (Vec (quote ii a) (quote ii n))
-----  VNil a         -> Nil (quote ii a)
-----  VCons a n x xs -> Cons (quote ii a) (quote ii n)
-----                         (quote ii x) (quote ii xs)
-----  VEq a x y      -> Inf (Eq (quote ii a) (quote ii x) (quote ii y))
-----  VRefl a x      -> Refl (quote ii a) (quote ii x)
-----  VFin n         -> Inf (Fin (quote ii n))
-----  VFZero n       -> FZero (quote ii n)
-----  VFSucc n f     -> FSucc  (quote ii n) (quote ii f)
  where
  -- Quote the arguments.
  neutralQuote :: Int -> Neutral -> ITerm
  neutralQuote ii x = case x of
    NFree v  -> Free v
    NQuote k -> Bound ((ii - k -1) `max` 0)
    NApp n v -> neutralQuote ii n :$: quote ii v
    NDataElim did mot met ts t -> DataElim did (quote ii mot) (map (quote ii) met) (map (quote ii) ts) (Inf$neutralQuote ii t)
-----    -- for hardcoded datatypes
-----    NNatElim m z s n
-----      -> NatElim (quote ii m) (quote ii z) (quote ii s)
-----                 (Inf (neutralQuote ii n))
-----    NVecElim a m mn mc n xs
-----      -> VecElim (quote ii a) (quote ii m)
-----                (quote ii mn) (quote ii mc)
-----                (quote ii n) (Inf (neutralQuote ii xs))
-----    NEqElim a m mr x y eq
-----      -> EqElim  (quote ii a) (quote ii m) (quote ii mr)
-----                (quote ii x) (quote ii y)
-----                (Inf (neutralQuote ii eq))
-----    NFinElim m mz ms n f
-----      -> FinElim (quote ii m)
-----                (quote ii mz) (quote ii ms)
-----                (quote ii n) (Inf (neutralQuote ii f))
  
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
iType g h = error $ "iType not defined for "++ show h  	  
--iType g (Data did args) = do zipM_ (cType g) args (type of arguments of the data type)
--                            return VStar
-- for hardcoded datatypes
-----iType g Nat                  = return VStar
-----iType g (NatElim m mz ms n)
-----  = do cType g m (VPi "pix" VNat (const VStar))
-----       let mVal = cEval m (fst g, []) 
-----       cType g mz (mVal `vapp` VZero)
-----       cType g ms (VPi "piy" VNat (\ k -> VPi "piz" (mVal `vapp` k) 
-----                                     (\_ -> mVal `vapp` VSucc k)))
-----       cType g n VNat
-----       let nVal = cEval n (fst g, [])
-----       return (mVal `vapp` nVal)
-----iType g (Vec a n)
-----  = do cType g a  VStar
-----       cType g n  VNat
-----       return VStar
-----iType g (VecElim a m mn mc n vs)
-----  = do cType g a VStar
-----       let aVal = cEval a (fst g, [])
-----       cType g m
-----             (VPi "" VNat (\n -> VPi "" (VVec aVal n) (\_ -> VStar)))
-----       let mVal = cEval m (fst g, [])
-----       cType g mn (foldl vapp mVal [VZero, VNil aVal])
-----       cType g mc
-----         (VPi "" VNat (\ n -> 
-----          VPi "" aVal (\ y -> 
-----          VPi "" (VVec aVal n) (\ ys ->
-----          VPi "" (foldl vapp mVal [n, ys]) (\_ ->
-----          (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
-----       cType g n VNat
-----       let nVal = cEval n (fst g, [])
-----       cType g vs (VVec aVal nVal)
-----       let vsVal = cEval vs (fst g, [])
-----       return (foldl vapp mVal [nVal, vsVal])
-----iType g (Eq a x y)
-----  = do cType g a VStar
-----       let aVal = cEval a (fst g, [])
-----       cType g x aVal
-----       cType g y aVal
-----       return VStar
-----iType g (EqElim a m mr x y eq)
-----  = do cType g a VStar
-----       let aVal = cEval a (fst g, [])
-----       cType g m
-----         (VPi "" aVal (\ x ->
-----          VPi ""aVal (\ y ->
-----          VPi ""(VEq aVal x y) (\_ -> VStar)))) 
-----       let mVal = cEval m (fst g, [])
-----       cType g mr
-----         (VPi "" aVal (\ x ->
-----          foldl vapp mVal [x, x]))
-----       cType g x aVal
-----       let xVal = cEval x (fst g, [])
-----       cType g y aVal
-----       let yVal = cEval y (fst g, [])
-----       cType g eq (VEq aVal xVal yVal)
-----       let eqVal = cEval eq (fst g, [])
-----       return (foldl vapp mVal [xVal, yVal])

-- Type check a checkable term.
cType :: (NameEnv Value, Context) -> CTerm -> Type -> Result ()
cType g (Inf e) v 
  = do v' <- iType g e
       unless ( quote0 v == quote0 v') (throwError ("type mismatch:\n"
                                        ++ "type inferred:  "
                                        ++ render (cPrint (quote0 v'))--  ++ "   sic:"++show (quote0 v')
                                        ++ "\n" ++ "type expected:  "
                                        ++ render (cPrint (quote0 v)) -- ++ "   sic:"++show (quote0 v)
                                        ++ "\n" ++ "for expression: " 
                                        ++ render (iPrint e)))
cType g (Lam vn e) ( VPi vnt ty ty')
  =    cType  ((\(d, g) -> (d, (vn, ty) : g)) g)
              (cSubst 0 (Free vn) e) (ty' (vfree vn))
-- FIXME PROBLEM: one of these is vnt?
-- FIXME boilerplate code?
-----cType g Zero      VNat              = return ()
-----cType g (Succ k)  VNat              = cType g k VNat
-----cType g (Nil a)   (VVec bVal VZero)
-----  = do  cType g a VStar
-----        let aVal = cEval a (fst g, []) 
-----        unless  (quote0 aVal == quote0 bVal) 
-----                (throwError "type mismatch")
-----cType g (Cons a n x xs) (VVec bVal (VSucc k))
-----  = do  cType g a VStar
-----        let aVal = cEval a (fst g, [])
-----        unless  (quote0 aVal == quote0 bVal)
-----                (throwError "type mismatch")
-----        cType g n VNat
-----        let nVal = cEval n (fst g, [])
-----        unless  (quote0 nVal == quote0 k)
-----                (throwError "number mismatch")
-----        cType g x aVal
-----        cType g xs (VVec bVal k)
-----cType g (Refl a z) (VEq bVal xVal yVal)
-----  = do  cType g a VStar
-----        let aVal = cEval a (fst g, [])
-----        unless  (quote0 aVal == quote0 bVal)
-----                (throwError "type mismatch")
-----        cType g z aVal
-----        let zVal = cEval z (fst g, [])
-----        unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
-----                (throwError "type mismatch")
cType g _ _
  = throwError "type mismatch"


prc_data :: DataInfo CTerm -> (NameEnv Value, Ctx Value) -> Result (NameEnv Value, Ctx Value)
prc_data dtinfo@(DataInfo nm ty ctors) = addTypeCons >=> addDataConsS >=> addEliminator
   where
         addTypeCons   :: (NameEnv Value, Ctx Value) -> Result (NameEnv Value, Ctx Value)
	 addTypeCons   (venv, tenv) 
	               = do let vty            = cEval ty (venv, [])
	                        (tyargs,tyres) = (renameKeys *** id) (vunprefixDummy vty)
	                        tyargsnames    = map fst tyargs
                            unless (quote0 tyres == infStar) $ throwError "data definition not defining a set"
                            let tyconsTP = (nm, vty)
		                tyconsVP = (nm, vabstract  tyargsnames (VTypeCons nm))
                            trace "     added Type Constructor." $ 
                            --trace ("type = " ++ show tyconsTP ++ "val="++show tyconsVP) $
                             return (tyconsVP : venv, tyconsTP : tenv)
         addDataConsS  :: (NameEnv Value, Ctx Value) -> Result (NameEnv Value, Ctx Value)
	 addDataConsS  = foldl (>=>) return (map addDataCons ctors)
         addDataCons   :: (String, CTerm) -> (NameEnv Value, Ctx Value) -> Result (NameEnv Value, Ctx Value)
	 addDataCons   (cnm,cty) (venv, tenv)
                       = do let cvty             = cEval cty (venv, [])
                                (ctyargs,ctyres) = (renameKeys *** id) (vunprefixDummy cvty)
                                ctyargsnames     = map fst ctyargs
                                cresMainTerm     = vmainty ctyres
                            unless (cresMainTerm == Just nm) $ 
                                throwError ("constructor " ++ cnm ++ " constructs values of type " ++ maybe "<no type>" show cresMainTerm ++ " instead of " ++ nm ++".")
                            cType (venv,ctyargs++tenv) (quote0 ctyres) (VStar)
                            let dataconsTP = (cnm,cvty)
                                dataconsVP = (cnm,vabstract ctyargsnames (VDataCons cnm))
                            trace "     added Data Constructor." $
                             --trace ("type = " ++ show dataconsTP ++ "val="++show dataconsVP) $
                             return (dataconsVP:venv, dataconsTP:tenv)
         addEliminator :: (NameEnv Value, Ctx Value) -> Result (NameEnv Value, Ctx Value)
	 addEliminator (venv, tenv) 
                       = do let vty        = cEval ty (venv,[])
                                tyargs'    = (fst.vunprefixDummy) vty
                                tyargs     = renameKeys tyargs'
                                tyargsname = map fst tyargs
                                enm        = nm ++ "Elim"
                                motV       = "P"
                                motT       = vprefix tyargs                 (\tas ->
                                             VPi "_" (vfree nm `vapps` tas) (\_   ->
                                             VStar ))
                                metVs      = map (('m':).fst) ctors
                                metTs  mot = map (methodTypeOf2 (venv,tenv) mot) ctors
                                metVTs mot = zip metVs (metTs mot)
                                tarV       =  vars !! (length . filter (=="_") . map fst $ tyargs') 
                                tarT tars  =  vfree nm `vapps` tars
                                elimTP = (enm, VPi motV motT        (\mot -> 
                                               vprefix (metVTs mot) (\met ->
                                               vprefix tyargs       (\ts  -> 
                                               VPi tarV (tarT ts)   (\tar ->
                                               mot `vapps` ts `vapp` tar )))))
                                elimVP = (enm, VLam  motV           (\mot -> 
                                               vabstract metVs      (\met -> 
                                               vabstract tyargsname (\ts  ->
                                               VLam  tarV           (\tar ->
                                               eliminate (venv,[]) dtinfo mot met ts tar )))))
                            trace "     added Eliminator." $
--                             trace ("type:" ++ show elimTP) $
  --                           trace ("val:"  ++ show elimVP) $
                             return (elimVP:venv, elimTP:tenv)
  
         methodTypeOf  :: (NameEnv Value, Ctx Value) -> Value {-motive-} -> (String,CTerm) {-Constructor-} -> Value {-Method Type-}
         methodTypeOf  (venv, tenv) mot (cnm,cty) 
                       = let vcty          = cEval cty (venv,[])
                             (dctyargs,dctyres) = (renameKeys *** id) (vunprefixDummy vcty)
                             vctyres   = vunprefixRes vcty
                             ctyres_args cas  = snd . fromJust . vunappty $ vctyres cas
                             --chirec        = map (maybe (False,[]) ((== nm) *** id).vunappty.snd) ctyargs
                             chirec cas       = map (maybe (False,[]) ((== nm) *** id).vunappty) cas
                             indargs cas = map (const "_" &&& (mot `vapps`)) (selrec cas)
                             selrec :: [Value] -> [[Value]]
                             selrec  cas = (map (uncurry (flip snoc)) . map (snd *** id) . filter (fst.fst))  ((zip (chirec cas) cas)::[((Bool,[Value]),Value)])
                         in  
                             vprefix dctyargs      (\cas   ->
                             vprefix (indargs cas) (\_     ->
                             mot `vapps` (ctyres_args cas) `vapp` (vfree cnm `vapps` cas)))
       --  methodTypeOf2  :: (NameEnv Value, Ctx Value) -> Value {-motive-} -> (String,CTerm) {-Constructor-} -> Value {-Method Type-}
       --  methodTypeOf2  (venv, tenv) mot (cnm,cty) = cEval (aux cty []) (("_$$_motive",mot):venv,[])
       --          where aux (Pi x a t) acc = let (f,as) = unapplies (unInf a) 
       --                                         newacc = if (f==Free nm) 
       --                                                     then acc ++ [Free "_$$_motive" `applies` as :$: Free x]
       --                                                     else acc
       --                                     in  Pi x a (aux t newacc)
         methodTypeOf2  :: (NameEnv Value, Ctx Value) -> Value {-motive-} -> (String,CTerm) {-Constructor-} -> Value {-Method Type-}
         methodTypeOf2  (venv, tenv) mot (cnm,cty) = aux (cEval cty (venv,[])) [] [] 0
                 where aux (VPi x a f) acc1 acc2 ii = let mt = vmainty a 
                                                          newacc v = if (mt==Just nm) 
                                                                      then let Just (t,as) = vunappty a
                                                                           in  acc1 ++ [("_",mot `vapps` as `vapp` v)]
                                                                      else acc1
                                                          (x',ii') = if x=="_" then (vars!!ii,ii+1) else (x,ii)
                                                     in VPi x' a (\v->aux (f v) (newacc v) (acc2++[v]) ii')
                       aux res         acc1 acc2 _ = let Just (_,as) = vunappty res
                                                     in vprefix acc1 (\_ -> mot `vapps` as `vapp` (vfree cnm `vapps` acc2))

	 rename ::  [String] -> [String] 
	 rename     = rename' vars
	 renameKeys :: [(String,x)] -> [(String,x)]
	 renameKeys = uncurry zip . (rename *** id) . unzip
     	 rename'  (v:vs) ("_":xs) = v : rename' vs xs 
     	 rename'  vs     (x:xs)   = x : rename' vs xs
     	 rename'  vs     []       = []
         vars = map (\x->[x]) (['x'..'z'] ++ ['a'..'w']) ++ map (('t':).show) [0..]


     	----let elimval        = (enm, VLam      motvar  (\mot ->
     	----                           vabstract metvars (\met -> 
     	----                           vabstract tsvars  (\ts  ->
     	----			   VLam      tvar    (\t   ->
     	----			   trace ("mot="++(show $    quote0 mot)) $
     	----			   trace ("met="++(show $map quote0 met)) $
     	----			   trace ("ts ="++(show $map quote0  ts)) $
     	----			   trace ("t  ="++(show $    quote0  t )) $
     	----			   iEval (DataElim dtinfo (quote mot) (map quote0 met) (map quote0 ts) (quote0 t)) 
     	----			         (dataconsvals++tyconsval:venv,[]) )))))
     	--let elimval        = (enm, cEval            (
     	--                           lam      (dataconsvals++tyconsval:venv) motvar  (\mot ->
     	--                           abstract (dataconsvals++tyconsval:venv) metvars (\met -> 
     	--                           abstract (dataconsvals++tyconsval:venv) tsvars  (\ts  ->
     	--			   lam      (dataconsvals++tyconsval:venv) tvar    (\t   ->
     	--			   Inf $ DataElim dtinfo mot met ts t))))) 
     	--			   (dataconsvals++tyconsval:venv,[]) )
        --     trace ("check elim=" ++ show elimval ++ " :: " ++show elimty) $ return 0
        --     trace  ("typecons: "   ++ show tyconsval    ++"  ::  " ++ show tyconsty    ++ 
        --           "\ndatacons: "   ++ show dataconsvals ++"  ::  " ++ show dataconstys ++ 
        --           "\neliminator: " ++ show elimval      ++"  ::  " ++ show elimty     )$
--    	return (elimval:dataconsvals ++ tyconsval:venv, elimty:dataconstys ++ tyconsty:tenv)
          


unInf (Inf t) = t

applies :: ITerm -> [CTerm] -> ITerm
applies = foldl (:$:) 

unapplies :: ITerm -> (ITerm,[CTerm])
unapplies (f :$: x) = (id *** snoc x) (unapplies f)
unapplies g = (g,[])

snoc x = (++ [x])

infixl 5 `vapp`
infixl 5 `vapps`
vapps :: Value -> [Value] -> Value
vapps = foldl vapp

vunapps :: Value -> (Value,[Value])
vunapps (VNeutral (NApp n v)) =  (id *** snoc v) (vunapps (VNeutral n))
vunapps x = (x,[])

vmainty :: Value -> Maybe String
vmainty = liftM fst . vunappty

vunappty :: Value -> Maybe (String,[Value])
vunappty (VTypeCons s l) = Just (s,l)
vunappty _               = Nothing

vabstract :: [String] -> ([Value] -> Value) -> Value
vabstract ns f = vabstract' ns f []
  where vabstract' (n:ns) f acc = VLam n (\x->vabstract' ns f (acc++[x])) 
        vabstract' []     f acc = f acc 




vprefix :: [(String, Value)] -> ([Value] -> Value) -> Value
vprefix ns f = vprefix' ns f []
  where vprefix' ((n,t):ns) f acc = VPi n t (\x->vprefix' ns f (acc++[x])) 
        vprefix' []         f acc = f acc 

vprefix2 :: [(String, [Value] -> Value)] -> ([Value] -> Value) -> Value
vprefix2 ns f = vprefix' ns f []
  where vprefix' ((n,t):ns) f acc = VPi n (t acc) (\x->vprefix' ns f (acc++[x])) 
        vprefix' []         f acc = f acc 


vunprefixDummy :: Type -> ([(String,Type)],Type)
vunprefixDummy (VPi x a f) = (((x,a):) *** id) (vunprefixDummy  (f (vfree x)))
vunprefixDummy x           = ([],x)



--vunprefixArgs :: Value -> [(String,[Value]->Value)]
--vunprefixArgs (VPi x a f) = (\vs -> vunprefixArgs (f )
--vunprefixArgs x           = []

vunprefixRes :: Value -> ([Value] -> Value)
vunprefixRes (VPi x a f) = \(v:vs) -> vunprefixRes (f v) vs
vunprefixRes x           = \[]     -> x


--vunprefix :: Value -> [Value] -> ([(String,Value)],Value)
--vunprefix (VPi x a f) = \(v:vs) -> (((x,a):) *** id) (vunprefix (f v) vs)
--vunprefix x           = \[]     -> ([],x)


---prefix :: [(String,CTerm)] -> CTerm -> CTerm
---prefix as r = foldr (\(x,a) b -> infPi x a b) r as


--unprefix :: CTerm -> ([(String,CTerm)],CTerm) 
--unprefix (Inf (Pi x a b)) = ( ((x,a):) *** id) (unprefix b) 
--unprefix x                = ([],x)

infPi x a b = Inf (Pi x a b)
infStar = Inf Star
infFree = Inf . Free
