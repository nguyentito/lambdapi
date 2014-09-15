module Printer where
-- {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
-- {-# LINE 154 "LP.lhs" #-}
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

import Term

-- {-# LINE 21 "Printer.lhs" #-}
vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]
-- {-# LINE 24 "Printer.lhs" #-}
parensIf :: Bool -> Doc -> Doc
parensIf True = PP.parens
parensIf False = id

-- {-# LINE 5 "Printer-LP.lhs" #-}
iPrint_ :: Int -> Int -> ITerm -> Doc
iPrint_ p ii (Ann c ty)       =  parensIf (p > 1) (cPrint_ 2 ii c <> text " :: " <> cPrint_ 0 ii ty)
iPrint_ p ii Star             =  text "*"
iPrint_ p ii (Pi d (Inf (Pi d' r)))
                               =  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint_ p ii (Pi d r)         =  parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d <> text " .", cPrint_ 0 (ii + 1) r])
iPrint_ p ii (Bound k)        =  text (vars !! (ii - k - 1))
iPrint_ p ii (Free (Global s))=  text s
iPrint_ p ii (i :$: c)         =  parensIf (p > 2) (sep [iPrint_ 2 ii i, nest 2 (cPrint_ 3 ii c)])
iPrint_ p ii Nat              =  text "Nat"
iPrint_ p ii (NatElim m z s n)=  iPrint_ p ii (Free (Global "natElim") :$: m :$: z :$: s :$: n)
iPrint_ p ii (Vec a n)        =  iPrint_ p ii (Free (Global "Vec") :$: a :$: n)
iPrint_ p ii (VecElim a m mn mc n xs)
                               =  iPrint_ p ii (Free (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
iPrint_ p ii (Eq a x y)       =  iPrint_ p ii (Free (Global "Eq") :$: a :$: x :$: y)
iPrint_ p ii (EqElim a m mr x y eq)
                               =  iPrint_ p ii (Free (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
iPrint_ p ii (Fin n)          =  iPrint_ p ii (Free (Global "Fin") :$: n)
iPrint_ p ii (FinElim m mz ms n f)
                               =  iPrint_ p ii (Free (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
iPrint_ p ii x                 =  text ("[" ++ show x ++ "]")
-- {-# LINE 28 "Printer-LP.lhs" #-}
cPrint_ :: Int -> Int -> CTerm -> Doc
cPrint_ p ii (Inf i)    = iPrint_ p ii i
cPrint_ p ii (Lam c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint_ 0 (ii + 1) c)
cPrint_ p ii Zero       = fromNat 0 ii Zero     --  text "Zero"
cPrint_ p ii (Succ n)   = fromNat 0 ii (Succ n) --  iPrint_ p ii (Free (Global "Succ") :$: n)
cPrint_ p ii (Nil a)    = iPrint_ p ii (Free (Global "Nil") :$: a)
cPrint_ p ii (Cons a n x xs) =
                           iPrint_ p ii (Free (Global "Cons") :$: a :$: n :$: x :$: xs)
cPrint_ p ii (Refl a x) = iPrint_ p ii (Free (Global "Refl") :$: a :$: x)
cPrint_ p ii (FZero n)  = iPrint_ p ii (Free (Global "FZero") :$: n)
cPrint_ p ii (FSucc n f)= iPrint_ p ii (Free (Global "FSucc") :$: n :$: f)
-- {-# LINE 40 "Printer-LP.lhs" #-}
fromNat :: Int -> Int -> CTerm -> Doc
fromNat n ii Zero = int n
fromNat n ii (Succ k) = fromNat (n + 1) ii k
fromNat n ii t = parensIf True (int n <> text " + " <> cPrint_ 0 ii t)
-- {-# LINE 45 "Printer-LP.lhs" #-}
nestedForall_ :: Int -> [(Int, CTerm)] -> CTerm -> Doc
nestedForall_ ii ds (Inf (Pi d r)) = nestedForall_ (ii + 1) ((ii, d) : ds) r
nestedForall_ ii ds x                = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint_ 0 n d) | (n,d) <- reverse ds] <> text " .", cPrint_ 0 ii x]

