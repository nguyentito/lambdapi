module Term where

data Name = Global String
          | Local Int
          | Quote Int
          deriving (Show, Eq)

data CTerm
   =  Inf  ITerm
   |  Lam  CTerm
-- {-# LINE 2 "CTermNat.lhs" #-}
   |  Zero
   |  Succ CTerm
-- {-# LINE 2 "CTermVec.lhs" #-}
  |  Nil CTerm
  |  Cons CTerm CTerm CTerm CTerm
-- {-# LINE 2 "CTermEq.lhs" #-}
   |  Refl CTerm CTerm
-- {-# LINE 2 "CTermFin.lhs" #-}
  |  FZero CTerm
  |  FSucc CTerm CTerm
-- {-# LINE 1523 "LP.lhs" #-}
  deriving (Show, Eq)
-- {-# LINE 1548 "LP.lhs" #-}
data ITerm
   =  Ann CTerm CTerm
   |  Star
   |  Pi CTerm CTerm
   |  Bound  Int
   |  Free  Name
   |  ITerm :$: CTerm
-- {-# LINE 2 "ITermNat.lhs" #-}
   |  Nat
   |  NatElim CTerm CTerm CTerm CTerm
-- {-# LINE 2 "ITermVec.lhs" #-}
  |  Vec CTerm CTerm
  |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm
-- {-# LINE 2 "ITermEq.lhs" #-}
   |  Eq CTerm CTerm CTerm
   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm
-- {-# LINE 2 "ITermFin.lhs" #-}
   |  Fin CTerm
   |  FinElim CTerm CTerm CTerm CTerm CTerm
-- {-# LINE 1564 "LP.lhs" #-}
  deriving (Show, Eq)
-- {-# LINE 1569 "LP.lhs" #-}
data Value
   =  VLam  (Value -> Value)
   |  VStar
   |  VPi Value (Value -> Value)
   |  VNeutral Neutral
-- {-# LINE 2 "ValueNat.lhs" #-}
  |  VNat
  |  VZero
  |  VSucc Value
-- {-# LINE 2 "ValueVec.lhs" #-}
  |  VNil Value
  |  VCons Value Value Value Value
  |  VVec Value Value
-- {-# LINE 2 "ValueEq.lhs" #-}
  |  VEq Value Value Value
  |  VRefl Value Value
-- {-# LINE 2 "ValueFin.lhs" #-}
  |  VFZero Value
  |  VFSucc Value Value
  |  VFin Value
-- {-# LINE 1582 "LP.lhs" #-}
data Neutral
   =  NFree  Name
   |  NApp  Neutral Value
-- {-# LINE 2 "NeutralNat.lhs" #-}
  |  NNatElim Value Value Value Neutral
-- {-# LINE 2 "NeutralVec.lhs" #-}
  |  NVecElim Value Value Value Value Value Neutral
-- {-# LINE 2 "NeutralEq.lhs" #-}
  |  NEqElim Value Value Value Value Value Neutral
-- {-# LINE 2 "NeutralFin.lhs" #-}
  |  NFinElim Value Value Value Value Neutral


  {-# LINE 5 "Interpreter.lhs" #-}
data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
  deriving (Show)

