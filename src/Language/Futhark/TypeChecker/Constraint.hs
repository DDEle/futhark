module Language.Futhark.TypeChecker.Constraint where

import Language.Futhark

data Constraint
  = (:==) StructType StructType
  | OneIsZero VName VName
  | Overloaded StructType [PrimType]
  deriving (Show, Eq)

type Constraints = [Constraint]
