module Parser where
-- {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
-- {-# LINE 154 "LP.lhs" #-}
import Control.Monad.Error
import Data.List
import Data.Char
-- {-# LINE 159 "LP.lhs" #-}
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
-- {-# LINE 164 "LP.lhs" #-}
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
-- {-# LINE 171 "LP.lhs" #-}
import System.Console.Readline
import System.IO hiding (print)

import Term
import LambdaPi

-- {-# LINE 5 "Parser.lhs" #-}
simplyTyped = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                              reservedNames = ["let", "assume", "putStrLn"] })
-- {-# LINE 9 "Parser.lhs" #-}
parseBindings :: CharParser () ([String], [Info])
parseBindings = 
                   (let rec :: [String] -> [Info] -> CharParser () ([String], [Info])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier simplyTyped 
                                         reserved simplyTyped "::"
                                         t <- pInfo
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec [] [])
                   <|>
                   do  x <- identifier simplyTyped 
                       reserved simplyTyped "::"
                       t <- pInfo
                       return ([x], [t])
  where
    pInfo = fmap HasType (parseType 0 []) <|> fmap (const (HasKind Star)) (reserved simplyTyped "*")
-- {-# LINE 30 "Parser.lhs" #-}
parseStmt :: [String] -> CharParser () (Stmt ITerm Info)
parseStmt e =
      do
        reserved simplyTyped "let"
        x <- identifier simplyTyped
        reserved simplyTyped "="
        t <- parseITerm 0 e
        return (Let x t)
  <|> do
        reserved simplyTyped "assume"
        (xs, ts) <- parseBindings
        return (Assume (reverse (zip xs ts)))
  <|> do
        reserved simplyTyped "putStrLn"
        x <- stringLiteral simplyTyped
        return (PutStrLn x)
  <|> do
        reserved lambdaPi "out"
        x <- option "" (stringLiteral simplyTyped)
        return (Out x)
  <|> fmap Eval (parseITerm 0 e)
-- {-# LINE 52 "Parser.lhs" #-}
parseType :: Int -> [String] -> CharParser () Type
parseType 0 e =
  try
     (do
        t <- parseType 1 e
        rest t <|> return t)
  where
    rest t =
      do
        reserved simplyTyped "->"
        t' <- parseType 0 e
        return (Fun t t')
parseType 1 e =
      do
        x <- identifier simplyTyped
        return (TFree (Global x))
  <|> parens simplyTyped (parseType 0 e)
-- {-# LINE 70 "Parser.lhs" #-}
parseITerm :: Int -> [String] -> CharParser () ITerm
parseITerm 0 e =
  try
     (do
        t <- parseITerm 1 e
        return t)
parseITerm 1 e =
  try
     (do
        t <- parseITerm 2 e
        rest (Inf t) <|> return t)
  <|> do
        t <- parens simplyTyped (parseLam e)
        rest t
  where
    rest t =
      do
        reserved simplyTyped "::"
        t' <- parseType 0 e
        return (Ann t t')
parseITerm 2 e =
      do
        t <- parseITerm 3 e
        ts <- many (parseCTerm 3 e)
        return (foldl (:@:) t ts)
parseITerm 3 e =
      do
        x <- identifier simplyTyped
        case findIndex (== x) e of
          Just n  -> return (Bound n)
          Nothing -> return (Free (Global x))
  <|> parens simplyTyped (parseITerm 0 e)

parseCTerm :: Int -> [String] -> CharParser () CTerm
parseCTerm 0 e =
      parseLam e
  <|> fmap Inf (parseITerm 0 e)
parseCTerm p e =
      try (parens simplyTyped (parseLam e))
  <|> fmap Inf (parseITerm p e)

parseLam :: [String] -> CharParser () CTerm
parseLam e =
      do reservedOp simplyTyped "\\"
         xs <- many1 (identifier simplyTyped)
         reservedOp simplyTyped "->"
         t <- parseCTerm 0 (reverse xs ++ e)
         --  reserved simplyTyped "."
         return (iterate Lam t !! length xs)
-- {-# LINE 122 "Parser.lhs" #-}
parseIO :: String -> CharParser () a -> String -> IO (Maybe a)
parseIO f p x = case P.parse (whiteSpace simplyTyped >> p >>= \ x -> eof >> return x) f x of
                  Left e  -> putStrLn (show e) >> return Nothing
                  Right r -> return (Just r)


-- {-# LINE 5 "Parser-LP.lhs" #-}
lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                           reservedNames = ["forall", "let", "assume", "putStrLn", "out"] })
-- {-# LINE 9 "Parser-LP.lhs" #-}
parseStmt_ :: [String] -> CharParser () (Stmt ITerm_ CTerm_)
parseStmt_ e =
      do
        reserved lambdaPi "let"
        x <- identifier lambdaPi
        reserved lambdaPi "="
        t <- parseITerm_ 0 e
        return (Let x t)
  <|> do
        reserved lambdaPi "assume"
        (xs, ts) <- parseBindings_ False [] 
        return (Assume (reverse (zip xs ts)))
  <|> do
        reserved lambdaPi "putStrLn"
        x <- stringLiteral lambdaPi
        return (PutStrLn x)
  <|> do
        reserved lambdaPi "out"
        x <- option "" (stringLiteral lambdaPi)
        return (Out x)
  <|> fmap Eval (parseITerm_ 0 e)
-- {-# LINE 31 "Parser-LP.lhs" #-}
parseBindings_ :: Bool -> [String] -> CharParser () ([String], [CTerm_])
parseBindings_ b e = 
                   (let rec :: [String] -> [CTerm_] -> CharParser () ([String], [CTerm_])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier lambdaPi
                                         reserved lambdaPi "::"
                                         t <- parseCTerm_ 0 (if b then e else [])
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec e [])
                   <|>
                   do  x <- identifier lambdaPi
                       reserved lambdaPi "::"
                       t <- parseCTerm_ 0 e
                       return (x : e, [t])
-- {-# LINE 50 "Parser-LP.lhs" #-}
parseITerm_ :: Int -> [String] -> CharParser () ITerm_
parseITerm_ 0 e =
      do
        reserved lambdaPi "forall"
        (fe,t:ts) <- parseBindings_ True e
        reserved lambdaPi "."
        t' <- parseCTerm_ 0 fe
        return (foldl (\ p t -> Pi_ t (Inf_ p)) (Pi_ t t') ts)
  <|>
  try
     (do
        t <- parseITerm_ 1 e
        rest (Inf_ t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam_ e)
        rest t
  where
    rest t =
      do
        reserved lambdaPi "->"
        t' <- parseCTerm_ 0 ([]:e)
        return (Pi_ t t')
parseITerm_ 1 e =
  try
     (do
        t <- parseITerm_ 2 e
        rest (Inf_ t) <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam_ e)
        rest t
  where
    rest t =
      do
        reserved lambdaPi "::"
        t' <- parseCTerm_ 0 e
        return (Ann_ t t')
parseITerm_ 2 e =
      do
        t <- parseITerm_ 3 e
        ts <- many (parseCTerm_ 3 e)
        return (foldl (:$:) t ts)
parseITerm_ 3 e =
      do
        reserved lambdaPi "*"
        return Star_
  <|> do
        n <- natural lambdaPi
        return (toNat_ n)
  <|> do
        x <- identifier lambdaPi
        case findIndex (== x) e of
          Just n  -> return (Bound_ n)
          Nothing -> return (Free_ (Global x))
  <|> parens lambdaPi (parseITerm_ 0 e)

parseCTerm_ :: Int -> [String] -> CharParser () CTerm_
parseCTerm_ 0 e =
      parseLam_ e
  <|> fmap Inf_ (parseITerm_ 0 e)
parseCTerm_ p e =
      try (parens lambdaPi (parseLam_ e))
  <|> fmap Inf_ (parseITerm_ p e)

parseLam_ :: [String] -> CharParser () CTerm_
parseLam_ e =
      do reservedOp lambdaPi "\\"
         xs <- many1 (identifier lambdaPi)
         reservedOp lambdaPi "->"
         t <- parseCTerm_ 0 (reverse xs ++ e)
         --  reserved lambdaPi "."
         return (iterate Lam_ t !! length xs)
-- {-# LINE 123 "Parser-LP.lhs" #-}
toNat_ :: Integer -> ITerm_
toNat_ n = Ann_ (toNat_' n) (Inf_ Nat_)
-- {-# LINE 126 "Parser-LP.lhs" #-}
toNat_' :: Integer -> CTerm_
toNat_' 0  =  Zero_
toNat_' n  =  Succ_ (toNat_' (n - 1))
