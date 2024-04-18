module Futhark.Analysis.View.Rules where

import Futhark.Analysis.View.Representation
import Debug.Trace (trace, traceM)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Bifunctor (bimap)
import qualified Data.List.NonEmpty as NE
import qualified Futhark.SoP.SoP as SoP
import Futhark.MonadFreshNames
import qualified Data.Map as M

normalise :: View -> ViewM View
normalise view =
  pure $ toNNF' $ idMap m view
  where
    m =
      ASTMapper
        { mapOnExp = normExp,
          mapOnVName = pure
        }
    normExp (Var x) = pure $ Var x
    normExp (x :&& y) = do
      x' <- normExp x
      y' <- normExp y
      case (x', y') of
        (Bool True, b) -> pure b
        (a, Bool True) -> pure a
        (Bool False, _) -> pure (Bool False)
        (_, Bool False) -> pure (Bool False)
        (a, b) | a == b ->
          pure a
        (a, b) | a == toNNF (Not b) -> -- A contradiction.
          pure (Bool False)
        (a, b) ->
          pure $ a :&& b
    normExp (x :|| y) = do
      x' <- normExp x
      y' <- normExp y
      case (x', y') of
        (Bool True, _) -> pure (Bool True)
        (_, Bool True) -> pure (Bool True)
        (Bool False, b) -> pure b
        (a, Bool False) -> pure a
        (a, b) -> pure $ a :|| b
    normExp x@(SoP2 _) = do
      x' <- astMap m x
      case x' of
        SoP2 sop -> pure . SoP2 . normaliseNegation . mergeSums $ sop
        _ -> pure x'
      where
        -- TODO extend this to find any 1 + -1*[[c]] without them being adjacent
        -- or the only terms.
        normaliseNegation sop -- 1 + -1*[[c]] => [[not c]]
          | [([], 1), ([Indicator c], -1)] <- getSoP sop =
            SoP.sym2SoP $ Indicator (Not c)
        normaliseNegation sop = sop

        -- Takes a sum of products which may have Sum terms and tries to absorb terms into
        -- those Sums. Time complexity is quadratic in the number of terms in the SoP.
        mergeSums sop =
          let sop' = getSoP sop
          in SoP.sopFromList $
               foldl (absorbTerm (applyFirstMatch [mergeUb, mergeLb])) [] sop'

        absorbTerm _ [] term = [term]
        absorbTerm f (t:ts) term
          | Just t' <- f t term =
            t':ts
        absorbTerm f (t:ts) term = t : absorbTerm f ts term

        -- Naively apply the first function with a Just result
        -- from a list of functions.
        applyFirstMatch :: [a -> a -> Maybe a] -> a -> a -> Maybe a
        applyFirstMatch [] _ _ = Nothing
        applyFirstMatch (f:fs) x y =
          case f x y of
            Nothing -> applyFirstMatch fs x y
            z -> z

        -- Rewrite sum_{j=lb}^ub e(j) + e(lb+1) ==> sum_{j=lb}^{ub+1} e(j).
        -- Relies on sorting of SoP and Exp to match.
        mergeUb ([Sum j lb ub e1], 1) ([e2], 1) =
            let ubp1 = ub SoP..+. SoP.int2SoP 1
            in  if substituteName j (SoP2 ubp1) e1 == e2
                then Just ([Sum j lb ubp1 e1], 1)
                else Nothing
        mergeUb _ _ = Nothing
        -- Rewrite sum_{j=lb}^ub e(j) + e(lb-1) ==> sum_{j=lb-1}^ub e(j).
        -- Relies on sorting of SoP and Exp to match.
        mergeLb ([Sum j lb ub e1], 1) ([e2], 1) =
            let lbm1 = lb SoP..-. SoP.int2SoP 1
            in  if substituteName j (SoP2 lbm1) e1 == e2
                then Just ([Sum j lbm1 ub e1], 1)
                else Nothing
        mergeLb _ _ = Nothing

        -- -- Rewrite sum e[lb:ub] + e[ub+1] ==> sum e[lb:ub+1].
        -- -- Relies on sorting of SoP and Exp to match.
        -- merge ([SumSlice x lb ub], 1) ([Idx y i], 1)
        --   | x == y,
        --     i == ub SoP..+. SoP.int2SoP 1 =
        --       Just ([SumSlice x lb i], 1)
        -- merge ([SumSlice x lb ub], 1) ([Idx y i], 1)
        --   | x == y,
        --     i == lb SoP..-. SoP.int2SoP 1 =
        --       Just ([SumSlice x i ub], 1)
        -- merge _ _ = Nothing
    normExp v = astMap m v

simplify :: View -> ViewM View
simplify view =
  removeDeadCases view
  >>= simplifyRule3
  >>= removeDeadCases
  >>= normalise

removeDeadCases :: View -> ViewM View
removeDeadCases (View it (Cases cases))
  | xs <- NE.filter f cases,
    not $ null xs,
    length xs /= length cases = -- Something actualy got removed.
  trace "👀 Removing dead cases" $
    pure $ View it $ Cases (NE.fromList xs)
  where
    f (Bool False, _) = False
    f _ = True
removeDeadCases view = pure view

-- TODO Maybe this should only apply to | True => 1 | False => 0
-- (and its negation)?
-- Applies if all case values are integer constants.
simplifyRule3 :: View -> ViewM View
simplifyRule3 v@(View _ (Cases ((Bool True, _) NE.:| []))) = pure v
simplifyRule3 (View it (Cases cases))
  | Just sops <- mapM (justConstant . snd) cases =
  let preds = NE.map fst cases
      sumOfIndicators =
        SoP.normalize . foldl1 (SoP..+.) . NE.toList $
          NE.zipWith
            (\p x -> SoP.sym2SoP (Indicator p) SoP..*. SoP.int2SoP x)
            preds
            sops
  in  trace "👀 Using Simplification Rule 3" $
        pure $ View it $ Cases (NE.singleton (Bool True, SoP2 sumOfIndicators))
  where
    justConstant (SoP2 sop) = SoP.justConstant sop
    justConstant _ = Nothing
simplifyRule3 v = pure v


rewriteRule4 :: View -> ViewM View
-- Rule 4 (recursive sum)
--
-- y = ∀i ∈ [b, b+1, ..., b + n - 1] .
--    | i == b => e              (e may depend on i)
--    | i /= b => y[i-1] + x[i]
-- _______________________________________________________________
-- y = ∀i ∈ [b, b+1, ..., b + n - 1] . e{b/i} + (Σ_{j=b+1}^i x[j])
--
-- If e{b/i} happens to be x[b] it later simplifies to
-- y = ∀i ∈ [b, b+1, ..., b + n - 1] . (Σ_{j=b}^i x[j])
rewriteRule4 (View it@(Forall i'' (Iota _)) (Cases cases))
  | (Var i :== b, e) :| [(Not (Var i' :== b'), x)] <- cases,
    Just x' <- justTermPlusRecurence x,
    i == i',
    i == i'',
    b == SoP2 (SoP.int2SoP 0), -- Domain is iota so b must be 0.
    b == b' = do
      traceM "👀 Using Rule 4 (recursive sum)"
      let lb = expToSoP b SoP..+. SoP.int2SoP 1 -- XXX change once Idx changes
      let ub = SoP.sym2SoP (Var i) -- XXX change once Idx changes
      j <- newNameFromString "j"
      let base = substituteName i b e
      let x'' = substituteName i (Var j) x'
      pure $ View it (toCases $ base ~+~ Sum j lb ub x'')
  where
    justTermPlusRecurence :: Exp -> Maybe Exp
    justTermPlusRecurence (SoP2 sop)
      | [([x], 1), ([Recurrence], 1)] <- getSoP sop =
          Just x
    justTermPlusRecurence _ = Nothing
rewriteRule4 view = pure view

rewrite :: View -> ViewM View
rewrite view =
  simplify view >>=
  rewriteRule4 >>=
  simplify

toNNF' :: View -> View
toNNF' (View i (Cases cs)) =
  View i (Cases (NE.map (bimap toNNF toNNF) cs))

-- -- y = ∀i ∈ [b, b+1, ..., b + n - 1] .
-- --    | i == b => e              (e may depend on i)
-- --    | i /= b => y[i-1] ⊕ x[i]
-- -- _______________________________________________________________
-- -- y = ∀i ∈ [b, b+1, ..., b + n - 1] . e{b/i} ⊕ (⊕[b+1:i] x)
-- --
-- -- If e{b/i} happens to be x[b] it later simplifies to
-- -- y = ∀i ∈ [b, b+1, ..., b + n - 1] . (⊕[b:i] x)
-- rewriteRule4 (View it@(Forall i'' (Iota _)) (Cases cases))
--   | (Var i :== b, e) :| [(Not (Var i' :== b'), x)] <- cases,
--     -- Just (Idx (Var x') (Var i''')) <- justTermPlusRecurence x,
--     Just (Indicator (Idx (Var x') (Var i'''))) <- justTermPlusRecurence x,
--     i == i',
--     i == i'',
--     i == i''',
--     b == SoP (SoP.int2SoP 0), -- Domain is iota so b must be 0.
--     b == b' = do
--       traceM "👀 Using Rule 4 (recursive sum)"
--       let lb = expToSoP b SoP..+. SoP.int2SoP 1 -- XXX change once Idx changes
--       let ub = SoP.sym2SoP (Var i) -- XXX change once Idx changes
--       base <- substituteName i b e
--       pure $ View it (toCases $ base ~+~ SumSlice x' lb ub)
--   where
--     justTermPlusRecurence :: Exp -> Maybe Exp
--     justTermPlusRecurence (SoP sop)
--       | [([x], 1), ([Recurrence], 1)] <- getSoP sop =
--           Just x
--     justTermPlusRecurence _ = Nothing
-- rewriteRule4 view = pure view