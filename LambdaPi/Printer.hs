module LambdaPi.Printer (iPrint, cPrint) where
import Interpreter.Types
import LambdaPi.Types 
import Control.Monad.Reader (Reader, runReader, local, ask)
import Control.Monad (liftM, liftM2)

import Prelude hiding (print)
import Text.PrettyPrint.HughesPJ (Doc)
import qualified Text.PrettyPrint.HughesPJ as PP (parens, int, sep, text, nest, (<>))

-- Monad versions of the used functions
-- Try to keep naming conventions:
-- http://haskell.org/ghc/docs/latest/html/libraries/base/Control-Monad.html#3
infixl 6 <>
(<>) = liftM2 (PP.<>)

textM :: String -> Reader [String] Doc
textM = return . PP.text

mparensIf :: Bool -> Reader [String] Doc -> Reader [String] Doc
mparensIf = liftM . parensIf

msep :: [Reader [String] Doc] -> Reader [String] Doc
msep = (liftM $ PP.sep) . sequence

intM :: Int -> Reader [String] Doc
intM = return . PP.int

mnest :: (Monad m) => Int -> m Doc -> m Doc
mnest x = liftM $ PP.nest x


iPrint :: ITerm -> Doc
iPrint t = runReader (iPrintM 0 t) []
                 
cPrint ::  CTerm -> Doc
cPrint t = runReader (cPrintM 0 t) []

iPrintM :: Int -> ITerm -> Reader [String] Doc
iPrintM p x = case x of
  Ann c ty        -> mparensIf (p > 1) (cPrintM 2 c <> textM " :: " <> cPrintM 0 ty)
  Star            -> textM "*"

  Pi vn d (Inf (Pi vn' d' r))
                  -> local (\x -> vn':vn:x) $
                      mparensIf (p > 0) (nestedForall 2  [(1,vn', d'), (0,vn, d)] r)

  Pi vn d r       -> mparensIf (p > 0) (msep [textM "forall " <> textM vn
                                       <> textM " :: " <> cPrintM 0 d
                                       <> textM " .", (local (\x -> vn:x) $ cPrintM 0 r)])
  Bound k         -> do
                       xs <- ask
                       textM (xs !! k)
  Free s          -> textM s
  i :$: c         -> mparensIf (p > 2)
                     (msep [iPrintM 2 i, mnest 2 (cPrintM 3 c)])
  Data did args     -> iPrintM p  (foldl (:$:) (Free did) args)
  DataElim did args -> iPrintM p  (foldl (:$:) (Free (did++"Elim")) args)
  Nat             -> textM "Nat"
  NatElim m z s n -> iPrintM p (Free "natElim" :$: m :$: z :$: s :$: n)
  Vec a n         -> iPrintM p (Free "Vec" :$: a :$: n)
  VecElim a m mn mc n xs
                  -> iPrintM p
                     (Free "vecElim" :$: a :$: m :$: mn :$: mc :$: n :$: xs)
  Eq a x y        -> iPrintM p (Free "Eq" :$: a :$: x :$: y)
  EqElim a m mr x y eq
                  -> iPrintM p 
                     (Free "eqElim" :$: a :$: m :$: mr :$: x :$: y :$: eq)
  Fin n           -> iPrintM p (Free "Fin" :$: n)
  FinElim m mz ms n f
                  ->  iPrintM p 
                      (Free "finElim" :$: m :$: mz :$: ms :$: n :$: f)


cPrintM :: Int -> CTerm -> Reader [String] Doc
cPrintM p  x = case x of
   Inf i         -> iPrintM p i
   Lam vn c      -> mparensIf (p > 0) $ textM "\\ " <> textM vn
                                        <> textM " -> "
                                        <> (local (\x -> vn:x) $ cPrintM 0 c)
   DataCons cid args -> iPrintM p  (foldl (:$:) (Free cid) args)
   Zero          -> fromNat 0 Zero
   Succ n        -> fromNat 0 (Succ n)
   Nil a         -> iPrintM p (Free "Nil"   :$: a)
   Cons a n x xs -> iPrintM p (Free "Cons"  :$: a :$: n :$: x :$: xs)
   Refl a x      -> iPrintM p (Free "Refl"  :$: a :$: x)
   FZero n       -> iPrintM p (Free "FZero" :$: n)
   FSucc n f     -> iPrintM p (Free "FSucc" :$: n :$: f)



parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

fromNat :: Int -> CTerm -> Reader [String] Doc
fromNat n Zero     = intM n
fromNat n (Succ k) = fromNat (n + 1) k
fromNat n t        = mparensIf True (intM n <> textM " + " <> cPrintM 0 t)

nestedForall :: Int -> [(Int, String, CTerm)] -> CTerm -> Reader [String] Doc
nestedForall ii ds (Inf (Pi vn d r)) = local (\x -> vn:x) $
                                        nestedForall (ii+1) ((ii,vn, d) : ds) r
nestedForall _  ds x
  = msep [textM "forall "
         <> msep [mparensIf True (textM vn <> textM " :: "
         <> (local (\xs -> drop (length ds-ii) xs) $ cPrintM 0 d)) | (ii,vn,d) <- reverse ds   ]
         <> textM " .", cPrintM 0 x]


