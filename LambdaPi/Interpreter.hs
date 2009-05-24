module LambdaPi.Interpreter where
import Interpreter.Types
import Interpreter.Runner
import LambdaPi.Types
import LambdaPi.Functions
import LambdaPi.Parser
import LambdaPi.Printer

lp :: Interpreter ITerm CTerm Value Value CTerm Value
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = curry iType,
         iquote = quote0,
         ieval = \ e x -> iEval x (e, []),
         ihastype = id,
         icprint = cPrint ,
         itprint = cPrint . quote0,
         iiparse = parseITerm 0 [],
         isparse = parseStmt [],
         iassume = \ s (x, t) -> lpassume s x t }

lpte :: Ctx Value
lpte =      [("Zero", VNat),
             ("Succ", VPi "pp" VNat (\_  -> VNat)),
             ("Nat", VStar),
             ("natElim", VPi "pp" (VPi "qq" VNat (\_  -> VStar)) (\ m ->
                               VPi "rr" (m `vapp` VZero) (\_  ->
                               VPi "ss" (VPi "tt" VNat (\ k -> VPi "uu" (m `vapp` k) (\_ -> (m `vapp` (VSucc k))))) ( \_ ->
                               VPi "vv" VNat (\ n -> m `vapp` n))))),
             ("Nil", VPi "pp" VStar (\ a -> VVec a VZero)),
             ("Cons", VPi "pp" VStar (\ a ->
                     VPi "qq" VNat (\ n ->
                     VPi "rr" a (\_  -> VPi "ss" (VVec a n) (\_ -> VVec a (VSucc n)))))),
             ("Vec", VPi "tt" VStar (\_ -> VPi "uu" VNat (\_ -> VStar))),
             ("vecElim", VPi "pp" VStar (\ a ->
                        VPi "qq" (VPi "rr" VNat (\ n -> VPi "ss" (VVec a n) (\_ -> VStar))) (\ m ->
                        VPi "tt" (m `vapp` VZero `vapp` (VNil a)) (\_ ->
                        VPi "uu" (VPi "vv" VNat (\ n ->
                              VPi "ww" a (\ x ->
                              VPi "xx" (VVec a n) (\ xs ->
                              VPi "yy" (m `vapp` n `vapp` xs) (\_ ->
                              m `vapp` VSucc n `vapp` VCons a n x xs))))) (\_ ->
                        VPi "zz" VNat (\ n ->
                        VPi "zzz" (VVec a n) (\ xs -> m `vapp` n `vapp` xs))))))),
             ("Refl", VPi "pp" VStar (\ a -> VPi "qq" a (\ x ->
                     VEq a x x))),
             ("Eq", VPi "pp" VStar (\ a -> VPi "qq" a (\ x -> VPi "rr" a (\ y -> VStar)))),
             ("eqElim", VPi "pp" VStar (\ a ->
                       VPi "qq" (VPi "rr" a (\ x -> VPi "ss" a (\ y -> VPi "tt" (VEq a x y) (\_ -> VStar)))) (\ m ->
                       VPi "uu" (VPi "vv" a (\ x -> m `vapp` x `vapp` x `vapp` VRefl a x)) (\_ ->
                       VPi "ww" a (\ x -> VPi "xx" a (\ y ->
                       VPi "yy" (VEq a x y) (\ eq ->
                       m `vapp` x `vapp` y `vapp` eq))))))),
             ("FZero", VPi "pp" VNat (\ n -> VFin (VSucc n))),
             ("FSucc", VPi "pp " VNat (\ n -> VPi "qq" (VFin n) (\ f ->
                      VFin (VSucc n)))),
             ("Fin", VPi "pp" VNat (\ n -> VStar)),
             ("finElim", VPi "pp" (VPi "qq" VNat (\ n -> VPi "rr" (VFin n) (\_ -> VStar))) (\ m ->
                        VPi "ss" (VPi "tt" VNat (\ n -> m `vapp` (VSucc n) `vapp` (VFZero n))) (\_ ->
                        VPi "uu" (VPi "vv" VNat (\ n -> VPi "ww" (VFin n) (\ f -> VPi "xx" (m `vapp` n `vapp` f) (\_ -> m `vapp` (VSucc n) `vapp` (VFSucc n f))))) (\_ ->
                        VPi "yy" VNat (\ n -> VPi "zz" (VFin n) (\ f ->
                        m `vapp` n `vapp` f))))))]

lpve :: Ctx Value
lpve =      [("Zero", VZero),
             ("Succ", VLam "aa" (\ n -> VSucc n)),
             ("Nat", VNat),
             ("natElim", cEval (Lam "aa" (Lam "bb" (Lam "cc" (Lam "dd" (Inf (NatElim (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))) ([], [])),
             ("Nil", VLam "bb" (\ a -> VNil a)),
             ("Cons", VLam "cc" (\ a -> VLam "dd" (\ n -> VLam "ee" (\ x -> VLam "ff" (\ xs ->
                     VCons a n x xs))))),
             ("Vec", VLam "gg" (\ a -> VLam "hh" (\ n -> VVec a n))),
             ("vecElim", cEval (Lam "aaa" (Lam "bbb" (Lam "ccc" (Lam "ddd" (Lam "eee" (Lam "fff" (Inf (VecElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             ("Refl", VLam "aaa" (\ a -> VLam "bbb" (\ x -> VRefl a x))),
             ("Eq", VLam "ccc" (\ a -> VLam "ddd" (\ x -> VLam "eee" (\ y -> VEq a x y)))),
             ("eqElim", cEval (Lam "aaaa" (Lam "bbbb" (Lam "cccc" (Lam "dddd" (Lam "eeee" (Lam "ffff" (Inf (EqElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             ("FZero", VLam "fff" (\ n -> VFZero n)),
             ("FSucc", VLam "ggg" (\ n -> VLam "hhh" (\ f -> VFSucc n f))),
             ("Fin", VLam "iii" (\ n -> VFin n)),
             ("finElim", cEval (Lam "aaaaa" (Lam "bbbbb" (Lam "ccccc" (Lam "ddddd" (Lam "eeeee" (Inf (FinElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[]))]

repLP :: IntCtx -> Bool -> IO ()
repLP ctx b = readevalprint ctx lp (b, [], lpve, lpte)

lpassume state@(inter, out, ve, te) x t =
  check lp state x (Ann t (Inf Star))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint 0 0 (quote0 v))))
        (\ (y, v) -> (inter, out, ve, (x, v) : te))
