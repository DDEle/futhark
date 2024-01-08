module Futhark.Solve.LP
  ( LP (..),
    LPE (..),
    convert,
    normalize,
    var,
    constant,
    cval,
    bin,
    or,
    (~+~),
    (~-~),
    (~*~),
    (!),
    neg,
    linearProgToLP,
    linearProgToLPE,
    LSum (..),
    LinearProg (..),
    OptType (..),
    Constraint (..),
    (==),
    (<=),
    (>=),
  )
where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V
import Futhark.Solve.Matrix (Matrix)
import Futhark.Solve.Matrix qualified as M
import Prelude hiding (or, (<=), (==), (>=))

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
    a' = a M.<|> M.diagonal (V.replicate (M.nrows a) 1)
    c' = c V.++ V.replicate (M.nrows a) 0

-- | Linear sum of variables.
newtype LSum v a = LSum {lsum :: (Map (Maybe v) a)}
  deriving (Show, Eq)

instance Functor (LSum v) where
  fmap f (LSum m) = LSum $ fmap f m

-- | Type of constraint
data CType = Equal | LessEq
  deriving (Show, Eq)

-- | A constraint for a linear program.
data Constraint v a
  = Constraint CType (LSum v a) (LSum v a)
  deriving (Show, Eq)

data OptType = Maximize | Minimize
  deriving (Show, Eq)

-- | A linear program.
data LinearProg v a = LinearProg
  { optType :: OptType,
    objective :: LSum v a,
    constraints :: [Constraint v a]
  }
  deriving (Show, Eq)

bigM :: (Num a) => a
bigM = 10 ^ 9

or :: (Eq a, Num a, Ord v) => v -> v -> Constraint v a -> Constraint v a -> [Constraint v a]
or b1 b2 c1 c2 =
  mkC b1 c1
    <> mkC b2 c2
    <> [var b1 ~+~ var b2 <= constant 1]
  where
    mkC b (Constraint Equal l r) =
      [ l <= r ~+~ bigM ~*~ (constant 1 ~-~ var b),
        l >= r ~-~ bigM ~*~ (constant 1 ~-~ var b)
      ]
    mkC b (Constraint LessEq l r) =
      [ l <= r ~+~ bigM ~*~ (constant 1 ~-~ var b)
      ]

bin :: (Num a, Ord v) => v -> Constraint v a
bin v = Constraint LessEq (var v) (constant 1)

(==) :: (Num a, Ord v) => LSum v a -> LSum v a -> Constraint v a
l == r = Constraint Equal l r

infix 4 ==

(<=) :: (Num a, Ord v) => LSum v a -> LSum v a -> Constraint v a
l <= r = Constraint LessEq l r

infix 4 <=

(>=) :: (Num a, Ord v) => LSum v a -> LSum v a -> Constraint v a
l >= r = Constraint LessEq (neg l) (neg r)

infix 4 >=

normalize :: (Eq a, Num a) => LSum v a -> LSum v a
normalize = LSum . Map.filter (/= 0) . lsum

var :: (Num a) => v -> LSum v a
var v = LSum $ Map.singleton (Just v) (fromInteger 1)

constant :: a -> LSum v a
constant = LSum . Map.singleton Nothing

cval :: (Num a, Ord v) => LSum v a -> a
cval = (! Nothing)

(~+~) :: (Eq a, Num a, Ord v) => LSum v a -> LSum v a -> LSum v a
(LSum x) ~+~ (LSum y) = normalize $ LSum $ Map.unionWith (+) x y

infixl 6 ~+~

(~-~) :: (Eq a, Num a, Ord v) => LSum v a -> LSum v a -> LSum v a
(LSum x) ~-~ (LSum y) = normalize $ LSum $ Map.unionWith (-) x y

infixl 6 ~-~

(~*~) :: (Eq a, Num a, Ord v) => a -> LSum v a -> LSum v a
a ~*~ s = normalize $ fmap (a *) s

infixl 7 ~*~

(!) :: (Num a, Ord v) => LSum v a -> Maybe v -> a
(LSum m) ! v =
  case m Map.!? v of
    Nothing -> 0
    Just a -> a

neg :: (Num a, Ord v) => LSum v a -> LSum v a
neg (LSum x) = LSum $ fmap negate x

-- | Converts a linear program given with a list of constraints
-- into the standard form.
--
-- TODO: Add Gaussian elimination to make sure the matrix in the
-- resulting 'LP' has linearly-independent rows.
linearProgToLP ::
  forall v a.
  (Unbox a, Num a, Ord v, Eq a) =>
  LinearProg v a ->
  LP a
linearProgToLP (LinearProg otype obj cs) =
  LP c a d
  where
    cs' = foldMap (convertEqCType . splitConstraint) cs
    idxMap =
      Map.fromList $
        zip [0 ..] $
          Map.keys $
            mconcat $
              map (lsum . fst) cs'
    mkRow s = V.generate (Map.size idxMap) $ \i -> s ! (idxMap Map.! i)
    c = mkRow $ convertObj otype obj
    a = M.fromVectors $ map (mkRow . fst) cs'
    d = V.fromList $ map snd cs'

    splitConstraint :: Constraint v a -> (CType, LSum v a, a)
    splitConstraint (Constraint ctype l r) =
      let c = negate $ cval (l ~-~ r)
       in (ctype, l ~-~ r ~-~ constant c, c)

    convertEqCType :: (CType, LSum v a, a) -> [(LSum v a, a)]
    convertEqCType (Equal, s, a) = [(s, a), (neg s, negate a)]
    convertEqCType (LessEq, s, a) = [(s, a)]

    convertObj :: OptType -> LSum v a -> LSum v a
    convertObj Maximize s = s
    convertObj Minimize s = neg s

-- | Converts a linear program given with a list of constraints
-- into the equational form. Assumes no <= constraints.
linearProgToLPE ::
  forall v a.
  (Unbox a, Num a, Ord v, Eq a) =>
  LinearProg v a ->
  LPE a
linearProgToLPE (LinearProg otype obj cs) =
  LPE c a d
  where
    cs' = map (checkOnlyEqType . splitConstraint) cs
    idxMap =
      Map.fromList $
        zip [0 ..] $
          Map.keys $
            mconcat $
              map (lsum . fst) cs'
    mkRow s = V.generate (Map.size idxMap) $ \i -> s ! (idxMap Map.! i)
    c = mkRow $ convertObj otype obj
    a = M.fromVectors $ map (mkRow . fst) cs'
    d = V.fromList $ map snd cs'

    splitConstraint :: Constraint v a -> (CType, LSum v a, a)
    splitConstraint (Constraint ctype l r) =
      let c = negate $ cval (l ~-~ r)
       in (ctype, l ~-~ r ~-~ constant c, c)

    checkOnlyEqType :: (CType, LSum v a, a) -> (LSum v a, a)
    checkOnlyEqType (Equal, s, a) = (s, a)
    checkOnlyEqType (ctype, _, _) = error $ show ctype

    convertObj :: OptType -> LSum v a -> LSum v a
    convertObj Maximize s = s
    convertObj Minimize s = neg s
