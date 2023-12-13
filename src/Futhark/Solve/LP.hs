module Futhark.Solve.LP
  ( LP (..),
    LPE (..),
    convert,
  )
where

import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V
import Futhark.Solve.Matrix

-- | A linear program. 'LP c a d' represents the program
--
-- > maximize c^T * a
-- > subject to a * x <= d
-- >            x >= 0
--
-- The matrix 'a' is assumed to have linearly-independent rows.
data LP a = LP
  { lpc :: Vector a,
    lpA :: Matrix a,
    lpd :: Vector a
  }
  deriving (Eq, Show)

-- | Equational form of a linear program. 'LPE c a d' represents the
-- program
--
-- > maximize c^T * a
-- > subject to a * x = d
-- >            x >= 0
--
-- The matrix 'a' is assumed to have linearly-independent rows.
data LPE a = LPE
  { pc :: Vector a,
    pA :: Matrix a,
    pd :: Vector a
  }
  deriving (Eq, Show)

-- | Converts an 'LP' into an equivalent 'LPE' by introducing slack
-- variables.
convert :: (Num a, Unbox a) => LP a -> LPE a
convert (LP c a d) = LPE c' a' d
  where
    a' = a <|> diagonal (V.replicate (nrows a) 1)
    c' = c V.++ V.replicate (nrows a) 0
