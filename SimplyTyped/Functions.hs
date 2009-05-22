module SimplyTyped.Functions where
import Interpreter.Types
import SimplyTyped.Types
import SimplyTyped.Printer

import Control.Monad.Error
import Text.PrettyPrint.HughesPJ hiding (parens)

putstrln x = putStrLn x

iEval :: ITerm -> (NameEnv Value,Env) -> Value
iEval (Ann  e _)    d  =  cEval e d
iEval (Free  x)     d  =  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
iEval (Bound  ii _) d  =  (snd d) !! ii
iEval (e1 :@: e2)   d  =  vapp (iEval e1 d) (cEval e2 d)

vapp :: Value -> Value -> Value
vapp (VLam _ f)    v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)

cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval (Inf  ii)   d  =  iEval ii d
cEval (Lam vn e)   d  =  VLam vn (\ x -> cEval e (((\(e, d) -> (e,  (x : d))) d)))

cKind :: Context -> Type -> Kind -> Result ()
cKind g (TFree x) Star
  =  case lookup x g of
       Just (HasKind Star)  ->  return ()
       Nothing              ->  throwError "unknown identifier"
cKind g (Fun kk kk') Star
  =  do  cKind g kk   Star
         cKind g kk'  Star

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Type
iType ii g (Ann e ty)
  =  do  cKind g ty Star
         cType ii g e ty
         return ty
iType ii g (Free x)
  =  case lookup x g of
       Just (HasType ty)  ->  return ty
       Nothing            ->  throwError "unknown identifier"
iType ii g (e1 :@: e2)
  =  do  si <- iType ii g e1
         case si of
           Fun ty ty'  ->  do  cType ii g e2 ty
                               return ty'
           _           ->  throwError "illegal application"

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType ii g (Inf e) ty
  =  do  ty' <- iType ii g e
         unless (ty == ty') (throwError "type mismatch")
cType ii g (Lam vn e) (Fun ty ty')
  =  cType  (ii + 1) ((Local ii vn, HasType ty) : g)
            (cSubst 0 (Free (Local ii vn)) e) ty'
--PROBLEM: CAPTURE?
cType ii g _ _
  =  throwError "type mismatch" 


iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii r (Ann e ty)   =  Ann (cSubst ii r e) ty
iSubst ii r (Bound j vn) =  if ii == j then r else Bound j vn
iSubst ii r (Free y)     =  Free y
iSubst ii r (e1 :@: e2)  =  iSubst ii r e1 :@: cSubst ii r e2

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii r (Inf e)      =  Inf (iSubst ii r e)
cSubst ii r (Lam vn e)   =  Lam vn (cSubst (ii + 1) r e)
--PROBLEM: CAPTURE

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam vn f)   =  Lam vn (quote (ii + 1) (f (vfree (Quote ii vn))))
quote ii (VNeutral n)  =  Inf (neutralQuote ii n)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree x)   =  boundfree ii x
neutralQuote ii (NApp n v)  =  neutralQuote ii n :@: quote ii v

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k vn)  =  Bound (ii - k - 1) vn
boundfree ii x             =  Free x

id'      =  Lam "xx" (Inf (Bound 0 "xx"))
const'   =  Lam "xxx" (Lam "yyy" (Inf (Bound 1 "xxx")))

tfree a  =  TFree (Global a)
free x   =  Inf (Free (Global x))

term1    =  Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y" 
term2    =  Ann const' (Fun  (Fun (tfree "b") (tfree "b"))
                             (Fun  (tfree "a")
                                   (Fun (tfree "b") (tfree "b"))))
            :@: id' :@: free "y" 

env1     =  [  (Global "y", HasType (tfree "a")),
               (Global "a", HasKind Star)]
env2     =  [(Global "b", HasKind Star)] ++ env1

test_eval1=  quote0 (iEval term1 ([],[]))
 {-  \eval{test_eval1}  -}

test_eval2=  quote0 (iEval term2 ([],[]))
 {-  \eval{test_eval2}  -}

test_type1=  iType0 env1 term1
 {-  \eval{test_type1}  -}

test_type2=  iType0 env2 term2
 {-  \eval{test_type2}  -}


