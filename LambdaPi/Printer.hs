module LambdaPi.Printer where
import Interpreter.Types
import LambdaPi.Types

import Prelude hiding (print)
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

--------------------------------------------------------------------------------
-- Print functions.
--------------------------------------------------------------------------------

-- Print an interable term.
iPrint :: ITerm -> Doc
iPrint = iPrint' 0 []
-- Print a checkable term.
cPrint :: CTerm -> Doc
cPrint = cPrint' 0 []

-- Print an interable term.
iPrint' :: Int -> [String] -> ITerm -> Doc
iPrint' p ctx x = case x of
  Ann c ty        -> parensIf (p > 1)
                     (cPrint' 2 ctx c <> text " :: " <> cPrint' 0 ctx ty)
  Star            -> text "*"
  Pi vn d (Inf (Pi vn' d' r))
                  -> parensIf (p > 0)
                     (nestedForall 2 (vn':vn:ctx) [(1,vn', d'), (0,vn, d)] r)
  Pi vn d r       -> parensIf (p > 0) (sep [text "forall " <> text vn
                                      <> text " :: " <> cPrint' 0 ctx d
                                      <> text " .", cPrint' 0 (vn:ctx) r])
  Bound k         -> text (ctx !! k)
  Free s          -> text s
  i :$: c         -> parensIf (p > 2)
                     (sep [iPrint' 2 ctx i, nest 2 (cPrint' 3 ctx c)])
  Nat             -> text "Nat"
  NatElim m z s n -> iPrint' p ctx (Free "natElim" :$: m :$: z :$: s :$: n)
  Vec a n         -> iPrint' p ctx (Free "Vec" :$: a :$: n)
  VecElim a m mn mc n xs
                  -> iPrint' p ctx
                     (Free "vecElim" :$: a :$: m :$: mn :$: mc :$: n :$: xs)
  Eq a x y        -> iPrint' p ctx (Free "Eq" :$: a :$: x :$: y)
  EqElim a m mr x y eq
                  -> iPrint' p ctx
                     (Free "eqElim" :$: a :$: m :$: mr :$: x :$: y :$: eq)
  Fin n           -> iPrint' p ctx (Free "Fin" :$: n)
  FinElim m mz ms n f
                  -> iPrint' p ctx
                     (Free "finElim" :$: m :$: mz :$: ms :$: n :$: f)

-- Print a checkable term.
cPrint' :: Int -> [String] -> CTerm -> Doc
cPrint' p ctx x = case x of
   Inf i         -> iPrint' p ctx i
   Lam vn c      -> parensIf (p > 0) $
                    text "\\ " <> text vn <> text " -> " <> cPrint' 0 (vn:ctx) c
   Zero          -> fromNat ctx Zero
   Succ n        -> fromNat ctx (Succ n)
   Nil a         -> iPrint' p ctx (Free "Nil" :$: a)
   Cons a n x xs -> iPrint' p ctx (Free "Cons" :$: a :$: n :$: x :$: xs)
   Refl a x      -> iPrint' p ctx (Free "Refl" :$: a :$: x)
   FZero n       -> iPrint' p ctx (Free "FZero" :$: n)
   FSucc n f     -> iPrint' p ctx (Free "FSucc" :$: n :$: f)

-- Print (..) under a condition
parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

-- Print a number which is represented in peano style, as a normal number.
fromNat :: [String] -> CTerm -> Doc
fromNat = fromNat' 0
  where
  fromNat' :: Int -> [String] -> CTerm -> Doc
  fromNat' n ctx Zero     = int n
  fromNat' n ctx (Succ k) = fromNat' (n + 1) ctx k
  fromNat' n ctx t        = parensIf True (int n <> text " + " <> cPrint' 0 ctx t)

nestedForall :: Int -> [String] -> [(Int,String, CTerm)] -> CTerm -> Doc
nestedForall ii ctx ds (Inf (Pi vn d r)) = nestedForall (ii+1) (vn:ctx) ((ii,vn, d) : ds) r
nestedForall _  ctx ds x                 = sep [text "forall " <> sep [parensIf True (text vn <> text " :: " <> cPrint' 0 (drop (length ds-ii) ctx) d) | (ii,vn,d) <- reverse ds] <> text " .", cPrint' 0 ctx x]

