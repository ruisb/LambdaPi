module LambdaPi.Printer where
import Interpreter.Types
import LambdaPi.Types

import Prelude hiding (print)
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

iPrint :: Int -> [String] -> ITerm -> Doc
iPrint p ctx (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ctx c <> text " :: " <> cPrint 0 ctx ty)
iPrint p ctx Star             =  text "*"
iPrint p ctx (Pi vn d (Inf (Pi vn' d' r)))
                               =  parensIf (p > 0) (nestedForall 2 (vn':vn:ctx) [(1,vn', d'), (0,vn, d)] r)
iPrint p ctx (Pi vn d r)         =  parensIf (p > 0) (sep [text "forall " <> text vn <> text " :: " <> cPrint 0 ctx d <> text " .", cPrint 0 (vn:ctx) r])
iPrint p ctx (Bound k)     =  text (ctx !! k) --(vars !! (ii - k - 1))
iPrint p ctx (Free s)=  text s
--iPrint p ctx (Free (Local _ s))=  text ('$':s)
iPrint p ctx (i :$: c)         =  parensIf (p > 2) (sep [iPrint 2 ctx i, nest 2 (cPrint 3 ctx c)])
iPrint p ctx Nat              =  text "Nat"
iPrint p ctx (NatElim m z s n)=  iPrint p ctx (Free "natElim" :$: m :$: z :$: s :$: n)
iPrint p ctx (Vec a n)        =  iPrint p ctx (Free "Vec" :$: a :$: n)
iPrint p ctx (VecElim a m mn mc n xs)
                               =  iPrint p ctx (Free "vecElim" :$: a :$: m :$: mn :$: mc :$: n :$: xs)
iPrint p ctx (Eq a x y)       =  iPrint p ctx (Free "Eq" :$: a :$: x :$: y)
iPrint p ctx (EqElim a m mr x y eq)
                               =  iPrint p ctx (Free "eqElim" :$: a :$: m :$: mr :$: x :$: y :$: eq)
iPrint p ctx (Fin n)          =  iPrint p ctx (Free "Fin" :$: n)
iPrint p ctx (FinElim m mz ms n f)
                               =  iPrint p ctx (Free "finElim" :$: m :$: mz :$: ms :$: n :$: f)
--iPrint p ctx x                 =  text ("[" ++ show x ++ "]")

cPrint :: Int -> [String] -> CTerm -> Doc
cPrint p ctx (Inf i)    = iPrint p ctx i
cPrint p ctx (Lam vn c) = parensIf (p > 0) (text "\\ " <> text vn {--CHANGED(vars !! ii)--} <> text " -> " <> cPrint 0 (vn:ctx) c)
cPrint p ctx Zero       = fromNat 0 ctx Zero     --  text "Zero"
cPrint p ctx (Succ n)   = fromNat 0 ctx (Succ n) --  iPrint p ctx (Free (Global "Succ") :$: n)
cPrint p ctx (Nil a)    = iPrint p ctx (Free "Nil" :$: a)
cPrint p ctx (Cons a n x xs) =
                           iPrint p ctx (Free  "Cons" :$: a :$: n :$: x :$: xs)
cPrint p ctx (Refl a x) = iPrint p ctx (Free "Refl" :$: a :$: x)
cPrint p ctx (FZero n)  = iPrint p ctx (Free "FZero" :$: n)
cPrint p ctx (FSucc n f)= iPrint p ctx (Free "FSucc" :$: n :$: f)

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

fromNat :: Int -> [String] -> CTerm -> Doc
fromNat n ctx Zero = int n
fromNat n ctx (Succ k) = fromNat (n + 1) ctx k
fromNat n ctx t = parensIf True (int n <> text " + " <> cPrint 0 ctx t)

nestedForall :: Int -> [String] -> [(Int,String, CTerm)] -> CTerm -> Doc
nestedForall ii ctx ds (Inf (Pi vn d r)) = nestedForall (ii+1) (vn:ctx) ((ii,vn, d) : ds) r
nestedForall _  ctx ds x                 = sep [text "forall " <> sep [parensIf True (text vn <> text " :: " <> cPrint 0 (drop (length ds-ii) ctx) d) | (ii,vn,d) <- reverse ds] <> text " .", cPrint 0 ctx x]

