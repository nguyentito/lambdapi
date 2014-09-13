module Printer where
  {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
  {-# LINE 154 "LP.lhs" #-}
import Control.Monad.Error
import Data.List
import Data.Char
  {-# LINE 159 "LP.lhs" #-}
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
  {-# LINE 164 "LP.lhs" #-}
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
  {-# LINE 171 "LP.lhs" #-}
import System.Console.Readline
import System.IO hiding (print)

import Term

{-# LINE 5 "Printer.lhs" #-}
tPrint :: Int -> Type -> Doc
tPrint p (TFree (Global s))  =  text s
tPrint p (Fun ty ty')        =  parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])
  {-# LINE 10 "Printer.lhs" #-}
iPrint :: Int -> Int -> ITerm -> Doc
iPrint p ii (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> tPrint 0 ty)
iPrint p ii (Bound k)        =  text (vars !! (ii - k - 1))
iPrint p ii (Free (Global s))=  text s
iPrint p ii (i :@: c)        =  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii x                =  text ("[" ++ show x ++ "]")
  {-# LINE 17 "Printer.lhs" #-}
cPrint :: Int -> Int -> CTerm -> Doc
cPrint p ii (Inf i)    = iPrint p ii i
cPrint p ii (Lam c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)
  {-# LINE 21 "Printer.lhs" #-}
vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]
  {-# LINE 24 "Printer.lhs" #-}
parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id
  {-# LINE 28 "Printer.lhs" #-}
print = render . cPrint 0 0
printType = render . tPrint 0
