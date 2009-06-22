module LambdaPi.Types where
import Interpreter.Types

zeronm = "Zero"
succnm = "Succ"

--------------------------------------------------------------------------------
-- The term types and the hardcoded basic types (Nat, Vector, Eq & Fin).
--------------------------------------------------------------------------------

-- Terms that can be checked with a type signature.
data CTerm
   =  Inf  ITerm
   |  Lam  String CTerm           -- A lambda expression
   -- constructors
 --HERE  |  DataCons ConsName [CTerm]
-----   -- The Nat constructors.
-----   |  Zero                        -- 0
-----   |  Succ CTerm                  -- +1
-----   -- The Vector constructors.
-----   |  Nil CTerm
-----   |  Cons CTerm CTerm CTerm CTerm
-----   -- The Equality constructors.
-----   |  Refl CTerm CTerm
-----   -- The Finite constructors.
-----   |  FZero CTerm
-----   |  FSucc CTerm CTerm
  deriving (Show, Eq)

-- Terms where the type signature can be infered.
data ITerm
   =  Ann CTerm CTerm                 -- Annotated terms.
   |  Star                            -- The type of types
   |  Pi String CTerm CTerm           -- Binding in dependent function space.
   |  Bound Int                       -- A bound variabele. Indexed with a
                                      -- 'de Bruijn indice'.
   |  Free Name                       -- A variabele that isn't bound.
   |  ITerm :$: CTerm                 -- Function application.
  --HERE |  TypeCons  DataTypeName [CTerm]
   |  DataElim  (DataInfo CTerm) -- datatype
                CTerm       -- motive
                [CTerm]     -- methods
                [CTerm]     -- targets
                CTerm       -- target
-----   -- Natural numbers
-----   |  Nat                             -- The Natural number type.
-----   |  NatElim CTerm CTerm CTerm CTerm -- The Natural number type eliminator.
-----   -- Vectors
-----   |  Vec CTerm CTerm                 -- The Vector type.
-----   |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm -- The Vector type eliminator.
-----   -- Equality
-----   |  Eq CTerm CTerm CTerm            -- The Equality type.
-----   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm -- The Equality type eliminator.
-----   -- Finite numbers
-----   |  Fin CTerm                       -- The Finite type
-----   |  FinElim CTerm CTerm CTerm CTerm CTerm -- The Finite type eliminator
  deriving (Show{--, Eq--})



instance Eq ITerm where
  Ann x y == Ann x' y' = x==x' && y==y'
  Star == Star = True
  Pi _ a b == Pi _ a' b' = a==a' && b==b' -- only difference compared to derived (Eq). We ignore the name here for equality.
  Bound n1 == Bound n2 = n1==n2
  Free n == Free n' = n==n'
  a :$: b == a':$:b' = a==a' && b==b'
  --HERE TypeCons x y == TypeCons x' y' = x==x' && y==y'
  DataElim a b  c d e == DataElim a' b' c' d' e' = a==a' && b==b' && c==c' && d==d' && e==e'
-----  Nat == Nat = True
-----  NatElim a b c d == NatElim a' b' c' d' = a==a' && b==b' && c == c' && d == d'
-----  Vec a b == Vec a' b' = a==a' && b ==b'
-----  VecElim a b c d e f == VecElim a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
-----  Eq a b c == Eq a' b' c' = a==a' && b==b' && c==c'
-----  EqElim a b c d e f == EqElim a' b' c' d' e' f' = a==a' && b==b' && c == c' && d == d' && e==e' && f==f'
-----  Fin a == Fin a' = a==a'
-----  FinElim a b c d e == FinElim a' b' c' d' e' = a==a' && b==b' && c == c' && d == d' && e == e'
  _ == _ = False 


-- The type of values.
data Value
   =  VLam String (Value -> Value)       -- Lambda abstraction
   |  VStar                              -- The type of types
   |  VPi String Value (Value -> Value)  -- Dependent function space
   |  VNeutral Neutral                   -- Neutral term
   |  VTypeCons DataTypeName [Value]
   |  VDataCons ConsName [Value]
------- Natural number values in peano style.
-----   |  VNat
-----   |  VZero
-----   |  VSucc Value
------- Vector values.
-----   |  VNil Value
-----   |  VCons Value Value Value Value
-----   |  VVec Value Value
------- Equality values.
-----   |  VEq Value Value Value
-----   |  VRefl Value Value
------- Finite values.
-----   |  VFZero Value
-----   |  VFSucc Value Value
-----   |  VFin Value

-- A Neutral term, i.e., a variable applied to a (possibly empty) sequence of
-- values.
data Neutral
   =  NFree  Name   -- Variable
   |  NQuote Int
   |  NApp  Neutral Value  -- An application of a neutral term to a value.
   |  NDataElim (DataInfo CTerm)  -- datatype
                Value         -- motive
                [Value]       -- methods
                [Value]       -- targets
                Neutral       -- target
------- Eliminator for neutral terms, to avoid the eval get stuck.
-----   |  NNatElim Value Value Value Neutral
-----   |  NVecElim Value Value Value Value Value Neutral
-----   |  NEqElim Value Value Value Value Value Neutral
-----   |  NFinElim Value Value Value Value Neutral

type Env = [Value]

type DataTypeName = String
type ConsName = String
