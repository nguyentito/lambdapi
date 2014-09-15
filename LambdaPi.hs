-- {-# LINE 149 "LP.lhs" #-}
module LambdaPi where
-- {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
-- {-# LINE 154 "LP.lhs" #-}
import Control.Monad.Error
-- {-# LINE 159 "LP.lhs" #-}
import Text.PrettyPrint.HughesPJ (render)

import Term
import Printer

-- added from Interpreter
type NameEnv v = [(Name, v)]

-- {-# LINE 888 "LP.lhs" #-}
type Result a = Either String a

-- {-# LINE 1620 "LP.lhs" #-}
type Env_ = [Value]

vapp_ :: Value -> Value -> Value
vapp_ (VLam f)      v  =  f v
vapp_ (VNeutral n)  v  =  VNeutral (NApp n v)

vfree_ :: Name -> Value
vfree_ n = VNeutral (NFree n)

cEval_ :: CTerm -> (NameEnv Value,Env_) -> Value
cEval_ (Inf  ii)    d  =  iEval_ ii d
cEval_ (Lam  c)     d  =  VLam (\ x -> cEval_ c (((\(e, d) -> (e,  (x : d))) d)))
-- {-# LINE 2 "cEval_Nat.lhs" #-}
cEval_ Zero      d  = VZero
cEval_ (Succ k)  d  = VSucc (cEval_ k d)
-- {-# LINE 2 "cEval_Vec.lhs" #-}
cEval_ (Nil a)          d  =  VNil (cEval_ a d)
cEval_ (Cons a n x xs)  d  =  VCons  (cEval_ a d) (cEval_ n d)
                                       (cEval_ x d) (cEval_ xs d)
-- {-# LINE 2 "cEval_Eq.lhs" #-}
cEval_ (Refl a x)       d  =  VRefl (cEval_ a d) (cEval_ x d)
-- {-# LINE 2 "cEval_Fin.lhs" #-}
cEval_ (FZero n)    d  =  VFZero (cEval_ n d)
cEval_ (FSucc n f)  d  =  VFSucc (cEval_ n d) (cEval_ f d)
-- {-# LINE 1654 "LP.lhs" #-}
iEval_ :: ITerm -> (NameEnv Value,Env_) -> Value
iEval_ (Ann  c _)       d  =  cEval_ c d
-- {-# LINE 1659 "LP.lhs" #-}
iEval_ Star           d  =  VStar   
iEval_ (Pi ty ty')    d  =  VPi (cEval_ ty d) (\ x -> cEval_ ty' (((\(e, d) -> (e,  (x : d))) d)))   
-- {-# LINE 1664 "LP.lhs" #-}
iEval_ (Free  x)      d  =  case lookup x (fst d) of Nothing ->  (vfree_ x); Just v -> v 
iEval_ (Bound  ii)    d  =  (snd d) !! ii
iEval_ (i :$: c)       d  =  vapp_ (iEval_ i d) (cEval_ c d)
-- {-# LINE 2 "iEval_Nat.lhs" #-}
iEval_ Nat                  d  =  VNat
iEval_ (NatElim m mz ms n)  d 
  =  let  mzVal = cEval_ mz d
          msVal = cEval_ ms d
          rec nVal =
            case nVal of
              VZero       ->  mzVal
              VSucc k     ->  msVal `vapp_` k `vapp_` rec k
              VNeutral n  ->  VNeutral
                               (NNatElim (cEval_ m d) mzVal msVal n)
              _            ->  error "internal: eval natElim"
     in   rec (cEval_ n d)
-- {-# LINE 3 "iEval_Vec.lhs" #-}
iEval_ (Vec a n)                 d  =  VVec (cEval_ a d) (cEval_ n d)
-- {-# LINE 7 "iEval_Vec.lhs" #-}
iEval_ (VecElim a m mn mc n xs)  d  =
  let  mnVal  =  cEval_ mn d
       mcVal  =  cEval_ mc d
       rec nVal xsVal =
         case xsVal of
           VNil _          ->  mnVal
           VCons _ k x xs  ->  foldl vapp_ mcVal [k, x, xs, rec k xs]
           VNeutral n      ->  VNeutral
                                (NVecElim  (cEval_ a d) (cEval_ m d)
                                            mnVal mcVal nVal n)
           _                ->  error "internal: eval vecElim"
  in   rec (cEval_ n d) (cEval_ xs d)
-- {-# LINE 2 "iEval_Eq.lhs" #-}
iEval_ (Eq a x y)                d  =  VEq (cEval_ a d) (cEval_ x d) (cEval_ y d)
iEval_ (EqElim a m mr x y eq)    d  =
  let  mrVal  =  cEval_ mr d
       rec eqVal =
         case eqVal of
           VRefl _ z -> mrVal `vapp_` z
           VNeutral n ->  
             VNeutral (NEqElim  (cEval_ a d) (cEval_ m d) mrVal
                                  (cEval_ x d) (cEval_ y d) n)
           _ -> error "internal: eval eqElim"
  in   rec (cEval_ eq d)
-- {-# LINE 2 "iEval_Fin.lhs" #-}
iEval_ (Fin n)                d  =  VFin (cEval_ n d)
iEval_ (FinElim m mz ms n f)  d  =
  let  mzVal  =  cEval_ mz d
       msVal  =  cEval_ ms d
       rec fVal =
         case fVal of
           VFZero k        ->  mzVal `vapp_` k
           VFSucc k g      ->  foldl vapp_ msVal [k, g, rec g]
           VNeutral n'     ->  VNeutral
                                (NFinElim  (cEval_ m d) (cEval_ mz d)
                                            (cEval_ ms d) (cEval_ n d) n')
           _                ->  error "internal: eval finElim"
  in   rec (cEval_ f d)
-- {-# LINE 1679 "LP.lhs" #-}
iSubst_ :: Int -> ITerm -> ITerm -> ITerm
iSubst_ ii i'   (Ann c c')     =  Ann (cSubst_ ii i' c) (cSubst_ ii i' c')
-- {-# LINE 1684 "LP.lhs" #-}

iSubst_ ii r  Star           =  Star  
iSubst_ ii r  (Pi ty ty')    =  Pi  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')
-- {-# LINE 1690 "LP.lhs" #-}
iSubst_ ii i' (Bound j)      =  if ii == j then i' else Bound j
iSubst_ ii i' (Free y)       =  Free y
iSubst_ ii i' (i :$: c)       =  iSubst_ ii i' i :$: cSubst_ ii i' c
-- {-# LINE 2 "iSubst_Nat.lhs" #-}
iSubst_ ii r  Nat            =  Nat
iSubst_ ii r  (NatElim m mz ms n)
                              =  NatElim (cSubst_ ii r m)
                                          (cSubst_ ii r mz) (cSubst_ ii r ms)
                                          (cSubst_ ii r ms)
-- {-# LINE 2 "iSubst_Vec.lhs" #-}
iSubst_ ii r  (Vec a n)      =  Vec (cSubst_ ii r a) (cSubst_ ii r n)
iSubst_ ii r  (VecElim a m mn mc n xs)
                              =  VecElim (cSubst_ ii r a) (cSubst_ ii r m)
                                          (cSubst_ ii r mn) (cSubst_ ii r mc)
                                          (cSubst_ ii r n) (cSubst_ ii r xs)
-- {-# LINE 2 "iSubst_Eq.lhs" #-}
iSubst_ ii r  (Eq a x y)     =  Eq (cSubst_ ii r a)
                                     (cSubst_ ii r x) (cSubst_ ii r y)
iSubst_ ii r  (EqElim a m mr x y eq)
                              =  VecElim (cSubst_ ii r a) (cSubst_ ii r m)
                                          (cSubst_ ii r mr) (cSubst_ ii r x)
                                          (cSubst_ ii r y) (cSubst_ ii r eq)
-- {-# LINE 2 "iSubst_Fin.lhs" #-}
iSubst_ ii r  (Fin n)        =  Fin (cSubst_ ii r n)
iSubst_ ii r  (FinElim m mz ms n f)
                              =  FinElim (cSubst_ ii r m)
                                          (cSubst_ ii r mz) (cSubst_ ii r ms)
                                          (cSubst_ ii r n) (cSubst_ ii r f)
-- {-# LINE 1701 "LP.lhs" #-}
cSubst_ :: Int -> ITerm -> CTerm -> CTerm
cSubst_ ii i' (Inf i)      =  Inf (iSubst_ ii i' i)
cSubst_ ii i' (Lam c)      =  Lam (cSubst_ (ii + 1) i' c)
-- {-# LINE 2 "cSubst_Nat.lhs" #-}
cSubst_ ii r  Zero         =  Zero
cSubst_ ii r  (Succ n)     =  Succ (cSubst_ ii r n)
-- {-# LINE 2 "cSubst_Vec.lhs" #-}
cSubst_ ii r  (Nil a)      =  Nil (cSubst_ ii r a)
cSubst_ ii r  (Cons a n x xs)
                            =  Cons (cSubst_ ii r a) (cSubst_ ii r x)
                                     (cSubst_ ii r x) (cSubst_ ii r xs)
-- {-# LINE 2 "cSubst_Eq.lhs" #-}
cSubst_ ii r  (Refl a x)   =  Refl (cSubst_ ii r a) (cSubst_ ii r x)
-- {-# LINE 2 "cSubst_Fin.lhs" #-}
cSubst_ ii r  (FZero n)    =  FZero (cSubst_ ii r n)
cSubst_ ii r  (FSucc n k)  =  FSucc (cSubst_ ii r n) (cSubst_ ii r k)
-- {-# LINE 1712 "LP.lhs" #-}
quote_ :: Int -> Value -> CTerm
quote_ ii (VLam t)
  =     Lam (quote_ (ii + 1) (t (vfree_ (Quote ii))))
-- {-# LINE 1718 "LP.lhs" #-}

quote_ ii VStar = Inf Star 
quote_ ii (VPi v f)                                       
    =  Inf (Pi (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii)))))  
-- {-# LINE 1725 "LP.lhs" #-}
quote_ ii (VNeutral n)
  =     Inf (neutralQuote_ ii n)
-- {-# LINE 2 "quote_Nat.lhs" #-}
quote_ ii VNat       =  Inf Nat
quote_ ii VZero      =  Zero
quote_ ii (VSucc n)  =  Succ (quote_ ii n)
-- {-# LINE 2 "quote_Vec.lhs" #-}
quote_ ii (VVec a n)         =  Inf (Vec (quote_ ii a) (quote_ ii n))
quote_ ii (VNil a)           =  Nil (quote_ ii a)
quote_ ii (VCons a n x xs)   =  Cons  (quote_ ii a) (quote_ ii n)
                                        (quote_ ii x) (quote_ ii xs)
-- {-# LINE 2 "quote_Eq.lhs" #-}
quote_ ii (VEq a x y)  =  Inf (Eq (quote_ ii a) (quote_ ii x) (quote_ ii y))
quote_ ii (VRefl a x)  =  Refl (quote_ ii a) (quote_ ii x)
-- {-# LINE 2 "quote_Fin.lhs" #-}
quote_ ii (VFin n)           =  Inf (Fin (quote_ ii n))
quote_ ii (VFZero n)         =  FZero (quote_ ii n)
quote_ ii (VFSucc n f)       =  FSucc  (quote_ ii n) (quote_ ii f)
-- {-# LINE 1735 "LP.lhs" #-}
neutralQuote_ :: Int -> Neutral -> ITerm
neutralQuote_ ii (NFree v)
   =  boundfree_ ii v
neutralQuote_ ii (NApp n v)
   =  neutralQuote_ ii n :$: quote_ ii v
-- {-# LINE 2 "neutralQuote_Nat.lhs" #-}
neutralQuote_ ii (NNatElim m z s n)
   =  NatElim (quote_ ii m) (quote_ ii z) (quote_ ii s) (Inf (neutralQuote_ ii n))
-- {-# LINE 2 "neutralQuote_Vec.lhs" #-}
neutralQuote_ ii (NVecElim a m mn mc n xs)
   =  VecElim (quote_ ii a) (quote_ ii m)
               (quote_ ii mn) (quote_ ii mc)
               (quote_ ii n) (Inf (neutralQuote_ ii xs))
-- {-# LINE 2 "neutralQuote_Eq.lhs" #-}
neutralQuote_ ii (NEqElim a m mr x y eq)
   =  EqElim  (quote_ ii a) (quote_ ii m) (quote_ ii mr)
               (quote_ ii x) (quote_ ii y)
               (Inf (neutralQuote_ ii eq))
-- {-# LINE 2 "neutralQuote_Fin.lhs" #-}
neutralQuote_ ii (NFinElim m mz ms n f)
   =  FinElim (quote_ ii m)
               (quote_ ii mz) (quote_ ii ms)
               (quote_ ii n) (Inf (neutralQuote_ ii f))
-- {-# LINE 1746 "LP.lhs" #-}
boundfree_ :: Int -> Name -> ITerm
boundfree_ ii (Quote k)     =  Bound ((ii - k - 1) `max` 0)
boundfree_ ii x             =  Free x
-- {-# LINE 1751 "LP.lhs" #-}
instance Show Value where
  show = show . quote0_
-- {-# LINE 1775 "LP.lhs" #-}
type Type     =  Value  
type Context_    =  [(Name, Type)]
-- {-# LINE 1818 "LP.lhs" #-}
quote0_ :: Value -> CTerm
quote0_ = quote_ 0 

iType0_ :: (NameEnv Value,Context_) -> ITerm -> Result Type
iType0_ = iType 0
-- {-# LINE 1826 "LP.lhs" #-}
iType :: Int -> (NameEnv Value,Context_) -> ITerm -> Result Type
iType ii g (Ann e tyt )
  =     do  cType  ii g tyt VStar
            let ty = cEval_ tyt (fst g, [])  
            cType ii g e ty
            return ty
iType ii g Star   
   =  return VStar   
iType ii g (Pi tyt tyt')  
   =  do  cType ii g tyt VStar    
          let ty = cEval_ tyt (fst g, [])  
          cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)  
                    (cSubst_ 0 (Free (Local ii)) tyt') VStar  
          return VStar   
iType ii g (Free x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint_ 0 0 (Free x)))
iType ii g (e1 :$: e2)
  =     do  si <- iType ii g e1
            case si of
              VPi  ty ty'  ->  do  cType ii g e2 ty
                                   return ( ty' (cEval_ e2 (fst g, [])))
              _                  ->  throwError "illegal application"
-- {-# LINE 2 "iTypeNat.lhs" #-}
iType ii g Nat                  =  return VStar
iType ii g (NatElim m mz ms n)  =
  do  cType ii g m (VPi VNat (const VStar))
      let mVal  = cEval_ m (fst g, []) 
      cType ii g mz (mVal `vapp_` VZero)
      cType ii g ms (VPi VNat (\ k -> VPi (mVal `vapp_` k) (\ _ -> mVal `vapp_` VSucc k)))
      cType ii g n VNat
      let nVal = cEval_ n (fst g, [])
      return (mVal `vapp_` nVal)
-- {-# LINE 2 "iTypeVec.lhs" #-}
iType ii g (Vec a n) =
  do  cType ii g a  VStar
      cType ii g n  VNat
      return VStar
iType ii g (VecElim a m mn mc n vs) =
  do  cType ii g a VStar
      let aVal = cEval_ a (fst g, [])
      cType ii g m
        (  VPi VNat (\n -> VPi (VVec aVal n) (\ _ -> VStar)))
      let mVal = cEval_ m (fst g, [])
      cType ii g mn (foldl vapp_ mVal [VZero, VNil aVal])
      cType ii g mc
        (  VPi VNat (\ n -> 
           VPi aVal (\ y -> 
           VPi (VVec aVal n) (\ ys ->
           VPi (foldl vapp_ mVal [n, ys]) (\ _ ->
           (foldl vapp_ mVal [VSucc n, VCons aVal n y ys]))))))
      cType ii g n VNat
      let nVal = cEval_ n (fst g, [])
      cType ii g vs (VVec aVal nVal)
      let vsVal = cEval_ vs (fst g, [])
      return (foldl vapp_ mVal [nVal, vsVal])
-- {-# LINE 2 "iTypeEq.lhs" #-}
iType i g (Eq a x y) =
  do  cType i g a VStar
      let aVal = cEval_ a (fst g, [])
      cType i g x aVal
      cType i g y aVal
      return VStar
iType i g (EqElim a m mr x y eq) =
  do  cType i g a VStar
      let aVal = cEval_ a (fst g, [])
      cType i g m
        (VPi aVal (\ x ->
         VPi aVal (\ y ->
         VPi (VEq aVal x y) (\ _ -> VStar)))) 
      let mVal = cEval_ m (fst g, [])
      cType i g mr
        (VPi aVal (\ x ->
         foldl vapp_ mVal [x, x]))
      cType i g x aVal
      let xVal = cEval_ x (fst g, [])
      cType i g y aVal
      let yVal = cEval_ y (fst g, [])
      cType i g eq (VEq aVal xVal yVal)
      let eqVal = cEval_ eq (fst g, [])
      return (foldl vapp_ mVal [xVal, yVal])
-- {-# LINE 1857 "LP.lhs" #-}

-- {-# LINE 1860 "LP.lhs" #-}
cType :: Int -> (NameEnv Value,Context_) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v 
  =     do  v' <- iType ii g e
            unless ( quote0_ v == quote0_ v') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint_ 0 0 (quote0_ v')) ++ "\n" ++ "type expected:  " ++ render (cPrint_ 0 0 (quote0_ v)) ++ "\n" ++ "for expression: " ++ render (iPrint_ 0 0 e)))
cType ii g (Lam e) ( VPi ty ty')
  =     cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty ) : g))) g)
                (cSubst_ 0 (Free (Local ii)) e) ( ty' (vfree_ (Local ii))) 
-- {-# LINE 2 "cTypeNat.lhs" #-}
cType ii g Zero      VNat  =  return ()
cType ii g (Succ k)  VNat  =  cType ii g k VNat
-- {-# LINE 2 "cTypeVec.lhs" #-}
cType ii g (Nil a) (VVec bVal VZero) =
  do  cType ii g a VStar
      let aVal = cEval_ a (fst g, []) 
      unless  (quote0_ aVal == quote0_ bVal) 
              (throwError "type mismatch")
cType ii g (Cons a n x xs) (VVec bVal (VSucc k)) =
  do  cType ii g a VStar
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType ii g n VNat
      let nVal = cEval_ n (fst g, [])
      unless  (quote0_ nVal == quote0_ k)
              (throwError "number mismatch")
      cType ii g x aVal
      cType ii g xs (VVec bVal k)
-- {-# LINE 2 "cTypeEq.lhs" #-}
cType ii g (Refl a z) (VEq bVal xVal yVal) =
  do  cType ii g a VStar
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType ii g z aVal
      let zVal = cEval_ z (fst g, [])
      unless  (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
              (throwError "type mismatch")
-- {-# LINE 1873 "LP.lhs" #-}
cType ii g _ _
  =     throwError "type mismatch"

