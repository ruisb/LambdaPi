module LambdaPi.Parser where
import LambdaPi.Types
import Interpreter.Types

import Data.List
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                           reservedNames = ["forall", "let", "assume", "putStrLn", "out"] })

parseStmt :: [String] -> CharParser () (Stmt ITerm CTerm)
parseStmt e =
      do
        reserved lambdaPi "let"
        x <- identifier lambdaPi
        reserved lambdaPi "="
        t <- parseITerm 0 e
        return (Let x t)
  <|> do
        reserved lambdaPi "assume"
        (xs, ts) <- parseBindings False [] 
        return (Assume (reverse (zip xs ts)))
  <|> do
        reserved lambdaPi "putStrLn"
        x <- stringLiteral lambdaPi
        return (PutStrLn x)
  <|> do
        reserved lambdaPi "out"
        x <- option "" (stringLiteral lambdaPi)
        return (Out x)
  <|> fmap Eval (parseITerm 0 e)

parseBindings :: Bool -> [String] -> CharParser () ([String], [CTerm])
parseBindings b e = 
                   (let rec :: [String] -> [CTerm] -> CharParser () ([String], [CTerm])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier lambdaPi
                                         reserved lambdaPi "::"
                                         t <- parseCTerm 0 (if b then e else [])
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec e [])
                   <|>
                   do  x <- identifier lambdaPi
                       reserved lambdaPi "::"
                       t <- parseCTerm 0 e
                       return (x : e, [t])

parseITerm :: Int -> [String] -> CharParser () ITerm
parseITerm 0 e =
      do
        reserved lambdaPi "forall"
        (vn:vns,t:ts) <- parseBindings True e
        reserved lambdaPi "."
        t' <- parseCTerm 0 (vn:vns)
        return (foldl (\ p (vn,t) -> Pi vn t (Inf p)) (Pi vn t t') (zip vns ts))
  <|>
  try
     (do
        t <- parseITerm 1 e
        rest (Inf t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam e)
        rest t
  where
    rest t =
      do
        reserved lambdaPi "->"
        t' <- parseCTerm 0 ([]:e)
        return (Pi "unnamed" t t')
parseITerm 1 e =
  try
     (do
        t <- parseITerm 2 e
        rest (Inf t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam e)
        rest t
  where
    rest t =
      do
        reserved lambdaPi "::"
        t' <- parseCTerm 0 e
        return (Ann t t')
parseITerm 2 e =
      do
        t <- parseITerm 3 e
        ts <- many (parseCTerm 3 e)
        return (foldl (:$:) t ts)
parseITerm 3 e =
      do
        reserved lambdaPi "*"
        return Star
  <|> do
        n <- natural lambdaPi
        return (toNat n)
  <|> do
        x <- identifier lambdaPi
        case findIndex (== x) e of
          Just n  -> return (Bound n "inventedboundname")
          Nothing -> return (Free (Global x))
  <|> parens lambdaPi (parseITerm 0 e)

parseCTerm :: Int -> [String] -> CharParser () CTerm
parseCTerm 0 e =
      parseLam e
  <|> fmap Inf (parseITerm 0 e)
parseCTerm p e =
      try (parens lambdaPi (parseLam e))
  <|> fmap Inf (parseITerm p e)

parseLam :: [String] -> CharParser () CTerm
parseLam e =
      do reservedOp lambdaPi "\\"
         xs <- many1 (identifier lambdaPi)
         reservedOp lambdaPi "->"
         t <- parseCTerm 0 (reverse xs ++ e)
         --  reserved lambdaPi "."
         --CHANGED return (iterate Lam t !! length xs)
         return (foldr ($) t (map Lam xs)) 

toNat :: Integer -> ITerm
toNat n = Ann (toNat' n) (Inf Nat)

toNat' :: Integer -> CTerm
toNat' 0  =  Zero
toNat' n  =  Succ (toNat' (n - 1))


