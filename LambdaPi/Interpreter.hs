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
         iitype = \ v c -> iType 0 (v, c),
         iquote = quote0,
         ieval = \ e x -> iEval x (e, []),
         ihastype = id,
         icprint = cPrint 0 0,
         itprint = cPrint 0 0 . quote0,
         iiparse = parseITerm 0 [],
         isparse = parseStmt [],
         iassume = \ s (x, t) -> lpassume s x t }

lpte :: Ctx Value
lpte =      [(Global "Zero", VNat),
             (Global "Succ", VPi "pp" VNat (\_  -> VNat)),
             (Global "Nat", VStar),
             (Global "natElim", VPi "pp" (VPi "qq" VNat (\_  -> VStar)) (\ m ->
                               VPi "rr" (m `vapp` VZero) (\_  ->
                               VPi "ss" (VPi "tt" VNat (\ k -> VPi "uu" (m `vapp` k) (\_ -> (m `vapp` (VSucc k))))) ( \_ ->
                               VPi "vv" VNat (\ n -> m `vapp` n))))),
             (Global "Nil", VPi "pp" VStar (\ a -> VVec a VZero)),
             (Global "Cons", VPi "pp" VStar (\ a ->
                            VPi "qq" VNat (\ n ->
                            VPi "rr" a (\_  -> VPi "ss" (VVec a n) (\_ -> VVec a (VSucc n)))))),
             (Global "Vec", VPi "tt" VStar (\_ -> VPi "uu" VNat (\_ -> VStar))),
             (Global "vecElim", VPi "pp" VStar (\ a ->
                               VPi "qq" (VPi "rr" VNat (\ n -> VPi "ss" (VVec a n) (\_ -> VStar))) (\ m ->
                               VPi "tt" (m `vapp` VZero `vapp` (VNil a)) (\_ ->
                               VPi "uu" (VPi "vv" VNat (\ n ->
                                     VPi "ww" a (\ x ->
                                     VPi "xx" (VVec a n) (\ xs ->
                                     VPi "yy" (m `vapp` n `vapp` xs) (\_ ->
                                     m `vapp` VSucc n `vapp` VCons a n x xs))))) (\_ ->
                               VPi "zz" VNat (\ n ->
                               VPi "zzz" (VVec a n) (\ xs -> m `vapp` n `vapp` xs))))))),
             (Global "Refl", VPi "pp" VStar (\ a -> VPi "qq" a (\ x ->
                            VEq a x x))),
             (Global "Eq", VPi "pp" VStar (\ a -> VPi "qq" a (\ x -> VPi "rr" a (\ y -> VStar)))),
             (Global "eqElim", VPi "pp" VStar (\ a ->
                              VPi "qq" (VPi "rr" a (\ x -> VPi "ss" a (\ y -> VPi "tt" (VEq a x y) (\_ -> VStar)))) (\ m ->
                              VPi "uu" (VPi "vv" a (\ x -> m `vapp` x `vapp` x `vapp` VRefl a x)) (\_ ->
                              VPi "ww" a (\ x -> VPi "xx" a (\ y ->
                              VPi "yy" (VEq a x y) (\ eq ->
                              m `vapp` x `vapp` y `vapp` eq))))))),
             (Global "FZero", VPi "pp" VNat (\ n -> VFin (VSucc n))),
             (Global "FSucc", VPi "pp " VNat (\ n -> VPi "qq" (VFin n) (\ f ->
                             VFin (VSucc n)))),
             (Global "Fin", VPi "pp" VNat (\ n -> VStar)),
             (Global "finElim", VPi "pp" (VPi "qq" VNat (\ n -> VPi "rr" (VFin n) (\_ -> VStar))) (\ m ->
                               VPi "ss" (VPi "tt" VNat (\ n -> m `vapp` (VSucc n) `vapp` (VFZero n))) (\_ ->
                               VPi "uu" (VPi "vv" VNat (\ n -> VPi "ww" (VFin n) (\ f -> VPi "xx" (m `vapp` n `vapp` f) (\_ -> m `vapp` (VSucc n) `vapp` (VFSucc n f))))) (\_ ->
                               VPi "yy" VNat (\ n -> VPi "zz" (VFin n) (\ f ->
                               m `vapp` n `vapp` f))))))]

lpve :: Ctx Value
lpve =      [(Global "Zero", VZero),
             (Global "Succ", VLam "aa" (\ n -> VSucc n)),
             (Global "Nat", VNat),
             (Global "natElim", cEval (Lam "aa" (Lam "bb" (Lam "cc" (Lam "dd" (Inf (NatElim (Inf (Bound 3 "aa")) (Inf (Bound 2 "bb")) (Inf (Bound 1 "cc")) (Inf (Bound 0 "dd")))))))) ([], [])),
             (Global "Nil", VLam "bb" (\ a -> VNil a)),
             (Global "Cons", VLam "cc" (\ a -> VLam "dd" (\ n -> VLam "ee" (\ x -> VLam "ff" (\ xs ->
                            VCons a n x xs))))),
             (Global "Vec", VLam "gg" (\ a -> VLam "hh" (\ n -> VVec a n))),
             (Global "vecElim", cEval (Lam "aaa" (Lam "bbb" (Lam "ccc" (Lam "ddd" (Lam "eee" (Lam "fff" (Inf (VecElim (Inf (Bound 5 "aaa")) (Inf (Bound 4 "bbb")) (Inf (Bound 3 "ccc")) (Inf (Bound 2 "ddd")) (Inf (Bound 1 "eee")) (Inf (Bound 0 "fff")))))))))) ([],[])),
             (Global "Refl", VLam "aaa" (\ a -> VLam "bbb" (\ x -> VRefl a x))),
             (Global "Eq", VLam "ccc" (\ a -> VLam "ddd" (\ x -> VLam "eee" (\ y -> VEq a x y)))),
             (Global "eqElim", cEval (Lam "aaaa" (Lam "bbbb" (Lam "cccc" (Lam "dddd" (Lam "eeee" (Lam "ffff" (Inf (EqElim (Inf (Bound 5 "aaaa")) (Inf (Bound 4 "bbbb")) (Inf (Bound 3 "cccc")) (Inf (Bound 2 "dddd")) (Inf (Bound 1 "eeee")) (Inf (Bound 0"ffff")))))))))) ([],[])),
             (Global "FZero", VLam "fff" (\ n -> VFZero n)),
             (Global "FSucc", VLam "ggg" (\ n -> VLam "hhh" (\ f -> VFSucc n f))),
             (Global "Fin", VLam "iii" (\ n -> VFin n)),
             (Global "finElim", cEval (Lam "aaaaa" (Lam "bbbbb" (Lam "ccccc" (Lam "ddddd" (Lam "eeeee" (Inf (FinElim (Inf (Bound 4 "aaaaa")) (Inf (Bound 3 "bbbbb")) (Inf (Bound 2 "ccccc")) (Inf (Bound 1 "ddddd")) (Inf (Bound 0 "eeeee"))))))))) ([],[]))]

repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)

lpassume state@(inter, out, ve, te) x t =
  check lp state x (Ann t (Inf Star))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint 0 0 (quote0 v))))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))
