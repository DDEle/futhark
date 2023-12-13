module Futhark.Solve.BranchAndBound (branchAndBound) where

import Data.Map qualified as M
import Data.Maybe
import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V
import Futhark.Solve.LP (LP (..))
import Futhark.Solve.Matrix
import Futhark.Solve.Simplex

newtype Bound a = Bound (Maybe a, Maybe a)

instance (Ord a) => Semigroup (Bound a) where
  Bound (mlb1, mub1) <> Bound (mlb2, mub2) =
    Bound (combine max mlb1 mlb2, combine min mub1 mub2)
    where
      combine _ Nothing b2 = b2
      combine _ b1 Nothing = b1
      combine c (Just b1) (Just b2) = Just $ c b1 b2

-- | Solves an LP with the additional constraint that all solutions
-- must be integral. Returns 'Nothing' if infeasible or unbounded.
branchAndBound ::
  (Read a, Unbox a, RealFrac a, Show a) =>
  LP a ->
  Maybe (a, Vector a)
branchAndBound prob@(LP _ a d) = (zopt,) <$> mopt
  where
    (zopt, mopt) = step [mempty] (negate $ read "Infinity") Nothing
    step [] zlow opt = (zlow, opt)
    step (next : todo) zlow opt =
      case simplexLP (mkProblem next) of
        Nothing -> step todo zlow opt
        Just (z, sol)
          | z <= zlow -> step todo zlow opt
          | V.all isInt sol ->
              step todo z (Just sol)
          | otherwise ->
              let (idx, frac) =
                    V.head $ V.filter (not . isInt . snd) $ V.zip (V.generate (V.length sol) id) sol
                  new_todo =
                    [ M.insertWith (<>) idx (Bound (Nothing, Just $ fromInteger $ floor frac)) next,
                      M.insertWith (<>) idx (Bound (Just $ fromInteger $ ceiling frac, Nothing)) next
                    ]
               in step (new_todo ++ todo) zlow opt

    isInt x = x == fromInteger (round x)
    mkProblem =
      M.foldrWithKey
        ( \idx bound acc -> addBound acc idx bound
        )
        prob

    addBound lp idx (Bound (mlb, mub)) =
      lp
        { lpA = a `addRows` new_rows,
          lpd = d V.++ V.fromList new_ds
        }
      where
        (new_rows, new_ds) =
          unzip $
            catMaybes
              [ (V.generate (ncols a) (\i -> if i == idx then (-1) else 0),) <$> (negate <$> mlb),
                (V.generate (ncols a) (\i -> if i == idx then 1 else 0),) <$> mub
              ]
