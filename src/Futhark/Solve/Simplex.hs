module Futhark.Solve.Simplex
  ( simplex,
    simplexLP,
  )
where

import Data.List qualified as L
import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V
import Futhark.Solve.LP
import Futhark.Solve.Matrix

-- | A tableau of an equational linear program @a * x = d@ is
--
-- > x @ b = p + q * x @ n
-- > ---------------------
-- > z = z' + r^T * x @ n
--
-- where @z = c^T * x@ and @b@ (@n@) is a vector containing the
-- indices of basic (nonbasic) variables.
--
-- The basic feasible solution corresponding to the above tableau is
-- given by @x \@ b = p@, @x \@n = 0@ with the value of the objective
-- equal to @z'@.

-- | Computes @r@ as given in the tableau above.
comp_r ::
  (Num a, Unbox a) =>
  LPE a ->
  Matrix a ->
  Vector Int ->
  Vector Int ->
  Vector a
comp_r (LPE c a _) invA_B b n =
  c @ n .-. c @ b .* invA_B .* a @ n

-- | @comp_q_enter prob invA_B b n enter@ computes the @enter@th
-- column of @q@.
comp_q_enter ::
  (Num a, Unbox a) =>
  LPE a ->
  Matrix a ->
  Int ->
  Vector a
comp_q_enter (LPE _ a _) invA_B enter =
  V.map negate $ invA_B *. getCol enter a

-- | Computes the objective given an inversion of @a@ and a basis.
comp_z ::
  (Num a, Unbox a) =>
  LPE a ->
  Matrix a ->
  Vector Int ->
  a
comp_z (LPE c _ d) invA_B b =
  c @ b .* invA_B <.> d

-- | Constructs an auxiliary equational linear program to compute the
-- initial feasible basis; returns the program along with a feasible
-- basis.
mkAux :: (Unbox a, Num a) => LPE a -> (LPE a, Vector Int, Vector Int)
mkAux (LPE _ a d) = (LPE c_aux a_aux d_aux, b_aux, n_aux)
  where
    c_aux = V.replicate (ncols a) 0 V.++ V.replicate (nrows a) (-1)
    d_aux = V.map abs d
    a_aux =
      imap (\r _ e -> signum (d V.! r) * e) a
        <|> identity (nrows a)
    b_aux = V.generate (nrows a) (+ ncols a)
    n_aux = V.generate (ncols a) id

-- | Finds an initial feasible basis for an equational linear program.
-- Returns 'Nothing' if the LP has no solution or the found basis is
-- degenerate and contains variables added by 'mkAux'.  Inverts some
-- equations by multiplying by -1 so it also returns a modified (but
-- equivalent) equational linear program.
findBasis ::
  (Unbox a, Ord a, Fractional a, Show a) =>
  LPE a ->
  Maybe (LPE a, Matrix a, Vector a, Vector Int, Vector Int)
findBasis prob = do
  (invA_B, p, b, n) <- step p_aux (invA_B_aux, d_aux, b_aux, n_aux)
  let prob' =
        prob
          { pc = pc prob,
            pA = sliceCols (V.generate (ncols $ pA prob) id) $ pA p_aux,
            pd = V.map abs $ pd prob
          }
  if comp_z p_aux invA_B b == 0 && V.maximum b < ncols (pA prob)
    then Just (prob', invA_B, p, b, V.filter (< ncols (pA prob)) n)
    else Nothing
  where
    (p_aux@(LPE _ _ d_aux), b_aux, n_aux) = mkAux prob
    invA_B_aux = identity $ V.length b_aux

-- | Solves an equational linear program. Returns 'Nothing' if the
-- program is infeasible or unbounded. Otherwise returns the optimal
-- value and the solution.
simplex ::
  (Unbox a, Ord a, Fractional a, Show a) =>
  LPE a ->
  Maybe (a, Vector a)
simplex prob = do
  (prob', invA_B, p, b, n) <- findBasis prob
  (invA_B', p', b', n') <- step prob' (invA_B, p, b, n)
  let z = comp_z prob' invA_B' b'
      sol =
        V.map snd $
          V.fromList $
            L.sortOn fst $
              V.toList $
                V.zip (b' V.++ n') (p' V.++ V.replicate (V.length n') 0)
  pure (z, sol)

-- | Solves a linear program.
simplexLP ::
  (Unbox a, Ord a, Fractional a, Show a) =>
  LP a ->
  Maybe (a, Vector a)
simplexLP lp = do
  (opt, sol) <- simplex lpe
  pure (opt, V.take (ncols $ lpA lp) sol)
  where
    lpe = convert lp

-- | One step of the simplex algorithm.
step ::
  (Unbox a, Ord a, Fractional a, Show a) =>
  LPE a ->
  (Matrix a, Vector a, Vector Int, Vector Int) ->
  Maybe (Matrix a, Vector a, Vector Int, Vector Int)
step prob (invA_B, p, b, n)
  | Just enter_idx <- menter_idx =
      let enter = n V.! enter_idx
          q_enter = comp_q_enter prob invA_B enter
          exit_idx =
            fst $
              V.minimumOn snd $
                V.map (\(i, p_', q_) -> (i, -(p_' / q_))) $
                  V.filter (\(_, _, q_) -> q_ < 0) $
                    V.zip3 (V.generate (V.length q_enter) id) p q_enter
          exit = b V.! exit_idx
          b' = b V.// [(exit_idx, enter)]
          n' = n V.// [(enter_idx, exit)]
          e_inv_vec =
            V.map
              (/ abs (q_enter V.! exit_idx))
              (q_enter V.// [(exit_idx, 1)])
          genF row col =
            (if row == exit_idx then 0 else invA_B ! (row, col))
              + (e_inv_vec V.! row) * invA_B ! (exit_idx, col)
          invA_B' = generate genF (nrows invA_B) (ncols invA_B)
          p' = p V.// [(exit_idx, 0)] .+. V.map (* (p V.! exit_idx)) e_inv_vec
       in if q_enter == V.map abs q_enter
            then Nothing
            else step prob (invA_B', p', b', n')
  | otherwise = Just (invA_B, p, b, n)
  where
    r = comp_r prob invA_B b n
    menter_idx = V.findIndex (> 0) r
