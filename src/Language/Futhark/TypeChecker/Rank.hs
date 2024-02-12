module Language.Futhark.TypeChecker.Rank (rankAnalysis) where

import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe
import Data.Vector.Unboxed qualified as V
import Debug.Trace
-- import Futhark.FreshNames qualified as FreshNames
-- import Futhark.MonadFreshNames hiding (newName)
import Futhark.Solve.BranchAndBound
import Futhark.Solve.LP hiding (Constraint, LSum, LinearProg)
import Futhark.Solve.LP qualified as LP
import Futhark.Solve.Simplex
import Language.Futhark hiding (ScalarType)
import Language.Futhark.TypeChecker.Constraints

-- import Language.Futhark.TypeChecker.Monad (mkTypeVarName)

type LSum = LP.LSum VName Double

type Constraint = LP.Constraint VName Double

type LinearProg = LP.LinearProg VName Double

type ScalarType = ScalarTypeBase SComp NoUniqueness

class Rank a where
  rank :: a -> LSum

instance Rank VName where
  rank = var

instance Rank SComp where
  rank SDim = constant 1
  rank (SVar v) = var v

instance Rank (Shape SComp) where
  rank = foldr (\d r -> rank d ~+~ r) (constant 0) . shapeDims

instance Rank ScalarType where
  rank Prim {} = constant 0
  rank (TypeVar _ (QualName [] v) []) = var v -- FIXME - might not be a type variable.
  rank (TypeVar {}) = constant 0
  rank (Arrow {}) = constant 0
  rank (Record {}) = constant 0
  rank (Sum {}) = constant 0

instance Rank Type where
  rank (Scalar t) = rank t
  rank (Array _ shape t) = rank shape ~+~ rank t

class Distribute a where
  distribute :: a -> a

instance Distribute Type where
  distribute = distributeOne
    where
      distributeOne (Array _ s (Arrow _ _ _ ta (RetType rd tr))) =
        Scalar $ Arrow NoUniqueness Unnamed mempty (arrayOf s ta) (RetType rd $ arrayOfWithAliases Nonunique s $ tr)
      distributeOne t = t

instance Distribute Ct where
  distribute (CtEq t1 t2) = distribute t1 `CtEq` distribute t2
  distribute c = c

data RankState = RankState
  { rankBinVars :: Map VName VName,
    rankCounter :: !Int,
    rankConstraints :: [Constraint]
  }

newtype RankM a = RankM {runRankM :: State RankState a}
  deriving (Functor, Applicative, Monad, MonadState RankState)

incCounter :: RankM Int
incCounter = do
  s <- get
  put s {rankCounter = rankCounter s + 1}
  pure $ rankCounter s

binVar :: VName -> RankM (VName)
binVar sv = do
  mbv <- (M.!? sv) <$> gets rankBinVars
  case mbv of
    Nothing -> do
      bv <- VName ("b_" <> baseName sv) <$> incCounter
      modify $ \s ->
        s
          { rankBinVars = M.insert sv bv $ rankBinVars s,
            rankConstraints = rankConstraints s ++ [bin bv]
          }
      pure bv
    Just bv -> pure bv

addConstraints :: [Constraint] -> RankM ()
addConstraints cs =
  modify $ \s -> s {rankConstraints = rankConstraints s ++ cs}

addConstraint :: Constraint -> RankM ()
addConstraint = addConstraints . pure

addCt :: Ct -> RankM ()
addCt (CtEq t1 t2) = addConstraint $ rank t1 ~==~ rank t2
addCt (CtAM r m) = do
  b_r <- binVar r
  b_m <- binVar m
  addConstraints $ oneIsZero (b_r, r) (b_m, m)

addTyVarInfo :: TyVar -> (Int, TyVarInfo) -> RankM ()
addTyVarInfo tv (_, TyVarFree) = pure ()
addTyVarInfo tv (_, TyVarPrim _) =
  addConstraint $ rank tv ~==~ constant 0
addTyVarInfo _ _ = error "Unhandled"

mkLinearProg :: Int -> [Ct] -> TyVars -> LinearProg
mkLinearProg counter cs tyVars =
  LP.LinearProg
    { optType = Minimize,
      objective =
        let shape_vars = M.keys $ rankBinVars finalState
         in foldr (\sv s -> var sv ~+~ s) (constant 0) shape_vars,
      constraints = rankConstraints finalState
    }
  where
    initState =
      RankState
        { rankBinVars = mempty,
          rankCounter = counter,
          rankConstraints = mempty
        }
    buildLP = do
      mapM_ addCt cs
      mapM_ (uncurry addTyVarInfo) $ M.toList tyVars
    finalState = flip execState initState $ runRankM buildLP

rankAnalysis :: Int -> [Ct] -> TyVars -> Maybe ([Ct], TyVars)
rankAnalysis counter cs tyVars = do
  traceM $ unlines ["rankAnalysis prog:", prettyString prog]
  (_size, ranks) <- branchAndBound lp
  let rank_map = (fromJust . (ranks V.!?)) <$> inv_var_map
  let (cs', SubstState tyVars') =
        flip runState (SubstState mempty) $
          runSubstM $
            substRanks rank_map $
              filter (not . isCtAM) cs
  pure (cs', tyVars <> tyVars')
  where
    isCtAM (CtAM {}) = True
    isCtAM _ = False
    splitFuncs
      ( CtEq
          (Scalar (Arrow _ _ _ t1a (RetType _ t1r)))
          (Scalar (Arrow _ _ _ t2a (RetType _ t2r)))
        ) =
        splitFuncs (CtEq t1a t2a) ++ splitFuncs (CtEq t1r' t2r')
        where
          t1r' = t1r `setUniqueness` NoUniqueness
          t2r' = t2r `setUniqueness` NoUniqueness
    splitFuncs c = [c]
    cs' = foldMap splitFuncs cs
    prog = mkLinearProg counter cs' tyVars
    (lp, var_map) = linearProgToLP prog
    inv_var_map = M.fromListWith (error "oh no!") [(v, k) | (k, v) <- M.toList var_map]

newtype SubstM a = SubstM {runSubstM :: State SubstState a}
  deriving (Functor, Applicative, Monad, MonadState SubstState)

data SubstState = SubstState
  { substTyVars :: TyVars
  }

rankToShape :: Map VName Int -> VName -> Shape SComp
rankToShape rs x = Shape $ replicate (rs M.! x) SDim

addRankInfo :: Map VName Int -> TyVar -> SubstM ()
addRankInfo rs t =
  modify $ \s -> s {substTyVars = M.insert t (lvl, TyVarRank $ rs M.! t) $ substTyVars s}
  where
    lvl = 0 -- FIXME

class SubstRanks a where
  substRanks :: Map VName Int -> a -> SubstM a

instance (SubstRanks a) => SubstRanks [a] where
  substRanks rs = mapM (substRanks rs)

instance SubstRanks (Shape SComp) where
  substRanks rs = pure . foldMap instDim
    where
      instDim (SDim) = Shape $ pure SDim
      instDim (SVar x) = rankToShape rs x

instance SubstRanks (TypeBase SComp u) where
  substRanks rs t@(Scalar (TypeVar u (QualName [] x) []))
    | rs M.! x > 0 = do
        addRankInfo rs x
        pure t
  substRanks rs (Scalar (Arrow u p d ta (RetType retdims tr))) = do
    ta' <- substRanks rs ta
    tr' <- substRanks rs tr
    pure $ Scalar (Arrow u p d ta' (RetType retdims tr'))
  substRanks rs (Array u shape t) = do
    shape' <- substRanks rs shape
    t' <- substRanks rs (Scalar t)
    pure $ arrayOfWithAliases u shape' t'
  substRanks _ t = pure t

instance SubstRanks Ct where
  substRanks rs (CtEq t1 t2) = CtEq <$> substRanks rs t1 <*> substRanks rs t2
  substRanks _ _ = error ""