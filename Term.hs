module Term where

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)
-- {-# LINE 705 "LP.lhs" #-}
data Type
   =  TFree  Name
   |  Fun    Type Type
  deriving (Show, Eq)
-- {-# LINE 712 "LP.lhs" #-}
data Value
   =  VLam      (Value -> Value)
   |  VNeutral  Neutral
-- {-# LINE 725 "LP.lhs" #-}
data Neutral
   =  NFree  Name
   |  NApp   Neutral Value
-- {-# LINE 732 "LP.lhs" #-}
vfree :: Name -> Value
vfree n = VNeutral (NFree n)
-- {-# LINE 786 "LP.lhs" #-}
data Kind = Star
  deriving (Show)

data Info
   =  HasKind  Kind
   |  HasType  Type 
  deriving (Show)


-- {-# LINE 670 "LP.lhs" #-}
data ITerm
   =  Ann    CTerm Type
   |  Bound  Int
   |  Free   Name
   |  ITerm :@: CTerm
  deriving (Show, Eq)

data CTerm
   =  Inf  ITerm 
   |  Lam  CTerm
  deriving (Show, Eq)


data CTerm_
   =  Inf_  ITerm_
   |  Lam_  CTerm_
-- {-# LINE 2 "CTerm_Nat.lhs" #-}
   |  Zero_
   |  Succ_ CTerm_
-- {-# LINE 2 "CTerm_Vec.lhs" #-}
  |  Nil_ CTerm_
  |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_
-- {-# LINE 2 "CTerm_Eq.lhs" #-}
   |  Refl_ CTerm_ CTerm_
-- {-# LINE 2 "CTerm_Fin.lhs" #-}
  |  FZero_ CTerm_
  |  FSucc_ CTerm_ CTerm_
-- {-# LINE 1523 "LP.lhs" #-}
  deriving (Show, Eq)
-- {-# LINE 1548 "LP.lhs" #-}
data ITerm_
   =  Ann_ CTerm_ CTerm_
   |  Star_
   |  Pi_ CTerm_ CTerm_
   |  Bound_  Int
   |  Free_  Name
   |  ITerm_ :$: CTerm_
-- {-# LINE 2 "ITerm_Nat.lhs" #-}
   |  Nat_
   |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_
-- {-# LINE 2 "ITerm_Vec.lhs" #-}
  |  Vec_ CTerm_ CTerm_
  |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
-- {-# LINE 2 "ITerm_Eq.lhs" #-}
   |  Eq_ CTerm_ CTerm_ CTerm_
   |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
-- {-# LINE 2 "ITerm_Fin.lhs" #-}
   |  Fin_ CTerm_
   |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
-- {-# LINE 1564 "LP.lhs" #-}
  deriving (Show, Eq)
-- {-# LINE 1569 "LP.lhs" #-}
data Value_
   =  VLam_  (Value_ -> Value_)
   |  VStar_
   |  VPi_ Value_ (Value_ -> Value_)
   |  VNeutral_ Neutral_
-- {-# LINE 2 "Value_Nat.lhs" #-}
  |  VNat_
  |  VZero_
  |  VSucc_ Value_
-- {-# LINE 2 "Value_Vec.lhs" #-}
  |  VNil_ Value_
  |  VCons_ Value_ Value_ Value_ Value_
  |  VVec_ Value_ Value_
-- {-# LINE 2 "Value_Eq.lhs" #-}
  |  VEq_ Value_ Value_ Value_
  |  VRefl_ Value_ Value_
-- {-# LINE 2 "Value_Fin.lhs" #-}
  |  VFZero_ Value_
  |  VFSucc_ Value_ Value_
  |  VFin_ Value_
-- {-# LINE 1582 "LP.lhs" #-}
data Neutral_
   =  NFree_  Name
   |  NApp_  Neutral_ Value_
-- {-# LINE 2 "Neutral_Nat.lhs" #-}
  |  NNatElim_ Value_ Value_ Value_ Neutral_
-- {-# LINE 2 "Neutral_Vec.lhs" #-}
  |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
-- {-# LINE 2 "Neutral_Eq.lhs" #-}
  |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
-- {-# LINE 2 "Neutral_Fin.lhs" #-}
  |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_


  {-# LINE 5 "Interpreter.lhs" #-}
data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
  deriving (Show)

