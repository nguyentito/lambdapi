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
iPrint :: Int -> Int -> ITerm -> Doc
iPrint p ii (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> cPrint 0 ii ty)
iPrint p ii Star             =  text "*"
iPrint p ii (Pi d (Inf (Pi d' r)))
                               =  parensIf (p > 0) (nestedForall (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint p ii (Pi d r)         =  parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint 0 ii d <> text " .", cPrint 0 (ii + 1) r])
iPrint p ii (Bound k)        =  text (vars !! (ii - k - 1))
iPrint p ii (Free (Global s))=  text s
iPrint p ii (i :$: c)         =  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii Nat              =  text "Nat"
iPrint p ii (NatElim m z s n)=  iPrint p ii (Free (Global "natElim") :$: m :$: z :$: s :$: n)
iPrint p ii (Vec a n)        =  iPrint p ii (Free (Global "Vec") :$: a :$: n)
iPrint p ii (VecElim a m mn mc n xs)
                               =  iPrint p ii (Free (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
iPrint p ii (Eq a x y)       =  iPrint p ii (Free (Global "Eq") :$: a :$: x :$: y)
iPrint p ii (EqElim a m mr x y eq)
                               =  iPrint p ii (Free (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
iPrint p ii (Fin n)          =  iPrint p ii (Free (Global "Fin") :$: n)
iPrint p ii (FinElim m mz ms n f)
                               =  iPrint p ii (Free (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
iPrint p ii x                 =  text ("[" ++ show x ++ "]")
-- {-# LINE 28 "Printer-LP.lhs" #-}
cPrint :: Int -> Int -> CTerm -> Doc
cPrint p ii (Inf i)    = iPrint p ii i
cPrint p ii (Lam c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)
cPrint p ii Zero       = fromNat 0 ii Zero     --  text "Zero"
cPrint p ii (Succ n)   = fromNat 0 ii (Succ n) --  iPrint p ii (Free (Global "Succ") :$: n)
cPrint p ii (Nil a)    = iPrint p ii (Free (Global "Nil") :$: a)
cPrint p ii (Cons a n x xs) =
                           iPrint p ii (Free (Global "Cons") :$: a :$: n :$: x :$: xs)
cPrint p ii (Refl a x) = iPrint p ii (Free (Global "Refl") :$: a :$: x)
cPrint p ii (FZero n)  = iPrint p ii (Free (Global "FZero") :$: n)
cPrint p ii (FSucc n f)= iPrint p ii (Free (Global "FSucc") :$: n :$: f)
-- {-# LINE 40 "Printer-LP.lhs" #-}
fromNat :: Int -> Int -> CTerm -> Doc
fromNat n ii Zero = int n
fromNat n ii (Succ k) = fromNat (n + 1) ii k
fromNat n ii t = parensIf True (int n <> text " + " <> cPrint 0 ii t)
-- {-# LINE 45 "Printer-LP.lhs" #-}
nestedForall :: Int -> [(Int, CTerm)] -> CTerm -> Doc
nestedForall ii ds (Inf (Pi d r)) = nestedForall (ii + 1) ((ii, d) : ds) r
nestedForall ii ds x                = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint 0 n d) | (n,d) <- reverse ds] <> text " .", cPrint 0 ii x]

