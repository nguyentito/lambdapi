module Parser where
-- {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
import Data.List
-- {-# LINE 164 "LP.lhs" #-}
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

import Term

-- {-# LINE 122 "Parser.lhs" #-}
parseIO :: String -> CharParser () a -> String -> IO (Maybe a)
parseIO f p x = case P.parse (spaces >> p >>= \x -> eof >> return x) f x of
  Left e -> putStrLn (show e) >> return Nothing
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
