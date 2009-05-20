module LambdaPi.Interpreter where
  import Interpreter.Types
  import Interpreter.Runner
  import LambdaPi.Types
  import LambdaPi.Functions
  import LambdaPi.Parser
  import LambdaPi.Printer

  lp :: Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
  lp = I { iname = "lambda-Pi",
           iprompt = "LP> ",
           iitype = \ v c -> iType_ 0 (v, c),
           iquote = quote0_,
           ieval = \ e x -> iEval_ x (e, []),
           ihastype = id,
           icprint = cPrint_ 0 0,
           itprint = cPrint_ 0 0 . quote0_,
           iiparse = parseITerm_ 0 [],
           isparse = parseStmt_ [],
           iassume = \ s (x, t) -> lpassume s x t }
 
  lpte :: Ctx Value_
  lpte =      [(Global "Zero", VNat_),
               (Global "Succ", VPi_ "pp" VNat_ (\ _ -> VNat_)),
               (Global "Nat", VStar_),
               (Global "natElim", VPi_ "pp" (VPi_ "qq" VNat_ (\ _ -> VStar_)) (\ m ->
                                 VPi_ "rr" (m `vapp_` VZero_) (\ _ ->
                                 VPi_ "ss" (VPi_ "tt" VNat_ (\ k -> VPi_ "uu" (m `vapp_` k) (\ _ -> (m `vapp_` (VSucc_ k))))) ( \ _ ->
                                 VPi_ "vv" VNat_ (\ n -> m `vapp_` n))))),
               (Global "Nil", VPi_ "pp" VStar_ (\ a -> VVec_ a VZero_)),
               (Global "Cons", VPi_ "pp" VStar_ (\ a ->
                              VPi_ "qq" VNat_ (\ n ->
                              VPi_ "rr" a (\ _ -> VPi_ "ss" (VVec_ a n) (\ _ -> VVec_ a (VSucc_ n)))))),
               (Global "Vec", VPi_ "tt" VStar_ (\ _ -> VPi_ "uu" VNat_ (\ _ -> VStar_))),
               (Global "vecElim", VPi_ "pp" VStar_ (\ a ->
                                 VPi_ "qq" (VPi_ "rr" VNat_ (\ n -> VPi_ "ss" (VVec_ a n) (\ _ -> VStar_))) (\ m ->
                                 VPi_ "tt" (m `vapp_` VZero_ `vapp_` (VNil_ a)) (\ _ ->
                                 VPi_ "uu" (VPi_ "vv" VNat_ (\ n ->
                                       VPi_ "ww" a (\ x ->
                                       VPi_ "xx" (VVec_ a n) (\ xs ->
                                       VPi_ "yy" (m `vapp_` n `vapp_` xs) (\ _ ->
                                       m `vapp_` VSucc_ n `vapp_` VCons_ a n x xs))))) (\ _ ->
                                 VPi_ "zz" VNat_ (\ n ->
                                 VPi_ "zzz" (VVec_ a n) (\ xs -> m `vapp_` n `vapp_` xs))))))),
               (Global "Refl", VPi_ "pp" VStar_ (\ a -> VPi_ "qq" a (\ x ->
                              VEq_ a x x))),
               (Global "Eq", VPi_ "pp" VStar_ (\ a -> VPi_ "qq" a (\ x -> VPi_ "rr" a (\ y -> VStar_)))),
               (Global "eqElim", VPi_ "pp" VStar_ (\ a ->
                                VPi_ "qq" (VPi_ "rr" a (\ x -> VPi_ "ss" a (\ y -> VPi_ "tt" (VEq_ a x y) (\ _ -> VStar_)))) (\ m ->
                                VPi_ "uu" (VPi_ "vv" a (\ x -> m `vapp_` x `vapp_` x `vapp_` VRefl_ a x)) (\ _ ->
                                VPi_ "ww" a (\ x -> VPi_ "xx" a (\ y ->
                                VPi_ "yy" (VEq_ a x y) (\ eq ->
                                m `vapp_` x `vapp_` y `vapp_` eq))))))),
               (Global "FZero", VPi_ "pp" VNat_ (\ n -> VFin_ (VSucc_ n))),
               (Global "FSucc", VPi_ "pp " VNat_ (\ n -> VPi_ "qq" (VFin_ n) (\ f ->
                               VFin_ (VSucc_ n)))),
               (Global "Fin", VPi_ "pp" VNat_ (\ n -> VStar_)),
               (Global "finElim", VPi_ "pp" (VPi_ "qq" VNat_ (\ n -> VPi_ "rr" (VFin_ n) (\ _ -> VStar_))) (\ m ->
                                 VPi_ "ss" (VPi_ "tt" VNat_ (\ n -> m `vapp_` (VSucc_ n) `vapp_` (VFZero_ n))) (\ _ ->
                                 VPi_ "uu" (VPi_ "vv" VNat_ (\ n -> VPi_ "ww" (VFin_ n) (\ f -> VPi_ "xx" (m `vapp_` n `vapp_` f) (\ _ -> m `vapp_` (VSucc_ n) `vapp_` (VFSucc_ n f))))) (\ _ ->
                                 VPi_ "yy" VNat_ (\ n -> VPi_ "zz" (VFin_ n) (\ f ->
                                 m `vapp_` n `vapp_` f))))))]
 
  lpve :: Ctx Value_
  lpve =      [(Global "Zero", VZero_),
               (Global "Succ", VLam_ "aa" (\ n -> VSucc_ n)),
               (Global "Nat", VNat_),
               (Global "natElim", cEval_ (Lam_ "aa" (Lam_ "bb" (Lam_ "cc" (Lam_ "dd" (Inf_ (NatElim_ (Inf_ (Bound_ 3 "aa")) (Inf_ (Bound_ 2 "bb")) (Inf_ (Bound_ 1 "cc")) (Inf_ (Bound_ 0 "dd")))))))) ([], [])),
               (Global "Nil", VLam_ "bb" (\ a -> VNil_ a)),
               (Global "Cons", VLam_ "cc" (\ a -> VLam_ "dd" (\ n -> VLam_ "ee" (\ x -> VLam_ "ff" (\ xs ->
                              VCons_ a n x xs))))),
               (Global "Vec", VLam_ "gg" (\ a -> VLam_ "hh" (\ n -> VVec_ a n))),
               (Global "vecElim", cEval_ (Lam_ "aaa" (Lam_ "bbb" (Lam_ "ccc" (Lam_ "ddd" (Lam_ "eee" (Lam_ "fff" (Inf_ (VecElim_ (Inf_ (Bound_ 5 "aaa")) (Inf_ (Bound_ 4 "bbb")) (Inf_ (Bound_ 3 "ccc")) (Inf_ (Bound_ 2 "ddd")) (Inf_ (Bound_ 1 "eee")) (Inf_ (Bound_ 0 "fff")))))))))) ([],[])),
               (Global "Refl", VLam_ "aaa" (\ a -> VLam_ "bbb" (\ x -> VRefl_ a x))),
               (Global "Eq", VLam_ "ccc" (\ a -> VLam_ "ddd" (\ x -> VLam_ "eee" (\ y -> VEq_ a x y)))),
               (Global "eqElim", cEval_ (Lam_ "aaaa" (Lam_ "bbbb" (Lam_ "cccc" (Lam_ "dddd" (Lam_ "eeee" (Lam_ "ffff" (Inf_ (EqElim_ (Inf_ (Bound_ 5 "aaaa")) (Inf_ (Bound_ 4 "bbbb")) (Inf_ (Bound_ 3 "cccc")) (Inf_ (Bound_ 2 "dddd")) (Inf_ (Bound_ 1 "eeee")) (Inf_ (Bound_ 0"ffff")))))))))) ([],[])),
               (Global "FZero", VLam_ "fff" (\ n -> VFZero_ n)),
               (Global "FSucc", VLam_ "ggg" (\ n -> VLam_ "hhh" (\ f -> VFSucc_ n f))),
               (Global "Fin", VLam_ "iii" (\ n -> VFin_ n)),
               (Global "finElim", cEval_ (Lam_ "aaaaa" (Lam_ "bbbbb" (Lam_ "ccccc" (Lam_ "ddddd" (Lam_ "eeeee" (Inf_ (FinElim_ (Inf_ (Bound_ 4 "aaaaa")) (Inf_ (Bound_ 3 "bbbbb")) (Inf_ (Bound_ 2 "ccccc")) (Inf_ (Bound_ 1 "ddddd")) (Inf_ (Bound_ 0 "eeeee"))))))))) ([],[]))]
{- LINE 225 "Interpreter.lhs" #-}
  repLP :: Bool -> IO ()
  repLP b = readevalprint lp (b, [], lpve, lpte)



  lpassume state@(inter, out, ve, te) x t =
    check lp state x (Ann_ t (Inf_ Star_))
          (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
          (\ (y, v) -> (inter, out, ve, (Global x, v) : te))
