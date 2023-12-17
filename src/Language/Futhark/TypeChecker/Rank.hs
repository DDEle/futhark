module Language.Futhark.TypeChecker.Rank where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector.Unboxed (Unbox)
import Data.Vector.Unboxed qualified as V
import Debug.Trace
import Futhark.MonadFreshNames hiding (newName, newVName)
import Futhark.Solve.BranchAndBound
import Futhark.Solve.LP (LP (..), LSum (..), LinearProg (..), OptType (..))
import Futhark.Solve.LP qualified as LP
import Language.Futhark
import Language.Futhark.TypeChecker.Constraint

data RankState = RankState
  { stateCounter :: !Int,
    stateBinMap :: Map VName VName,
    stateConstraints :: [LP.Constraint VName Double],
    stateObjSet :: Set VName
  }
  deriving (Show, Eq)

newtype RankM a
  = RankM (State RankState a)
  deriving
    ( Monad,
      Functor,
      Applicative,
      MonadState RankState
    )

runRankM :: RankM a -> RankState -> a
runRankM (RankM m) = evalState m

class Rank a b where
  mkRank :: a -> LSum VName b

instance (Num b) => Rank (Shape d) b where
  mkRank = LP.constant . fromIntegral . shapeRank

instance (Num b) => Rank (ScalarTypeBase dim u) b where
  mkRank (TypeVar _ (QualName _ vn) []) =
    LP.var vn
  mkRank t@(TypeVar {}) = error ""
  mkRank _ = LP.constant 0

instance (Num b, Eq b) => Rank (TypeBase dim u) b where
  mkRank (Scalar t) = mkRank t
  mkRank (Array _ shape t) =
    mkRank shape LP.~+~ mkRank t

addConstraints :: [LP.Constraint VName Double] -> RankM ()
addConstraints cs = modify $ \env ->
  env
    { stateConstraints =
        stateConstraints env ++ cs
    }

addConstraint :: LP.Constraint VName Double -> RankM ()
addConstraint c = addConstraints [c]

incCounter :: RankM Int
incCounter = do
  s <- get
  put s {stateCounter = stateCounter s + 1}
  pure $ stateCounter s

newVName :: String -> RankM VName
newVName s = do
  i <- incCounter
  pure $ VName (nameFromString s) i

binVar :: VName -> RankM (VName)
binVar v = do
  bm <- gets stateBinMap
  case bm M.!? v of
    Nothing -> do
      b <- newVName (baseString v <> "_b")
      modify $ \senv ->
        senv
          { stateBinMap = M.insert v b bm
          }
      addConstraint $ LP.var b LP.<= LP.constant 1
      pure b
    Just b -> pure b

addToObjSet :: VName -> RankM ()
addToObjSet v =
  modify $ \senv -> senv {stateObjSet = S.insert v $ stateObjSet senv}

rankLP ::
  (Num b, Eq b, Unbox b) =>
  Constraints ->
  RankM (LP b, Map Int VName)
rankLP cs = do
  cs' <- concat <$> mapM convertConstraint cs
  obj <- (LSum . M.fromList . map ((,1) . Just) . S.toList) <$> gets stateObjSet
  pure $
    LP.linearProgToLP $
      LinearProg
        { optType = LP.Minimize,
          objective = obj,
          constraints = cs'
        }
  where
    convertConstraint (t1 :== t2) =
      pure [mkRank t1 LP.== mkRank t2]
    convertConstraint (OneIsZero s1 s2) = do
      b1 <- binVar s1
      b2 <- binVar s2
      addToObjSet s1
      addToObjSet s2
      pure $
        LP.or
          b1
          b2
          (LP.var s1 LP.== LP.constant 0)
          (LP.var s2 LP.== LP.constant 0)
    convertConstraint (Overloaded t _) =
      pure [mkRank t LP.== LP.constant 0]

solveRanks :: Constraints -> Maybe (Map VName Int)
solveRanks cs =
  flip runRankM initState $ do
    (lp, idxMap) <- rankLP cs
    traceM $ unlines ["rcs: " <> show cs, "rlp : " <> show lp]
    pure $ do
      (z :: Double, sol) <- branchAndBound lp
      pure $ M.fromList $ map (\(i, x) -> (idxMap M.! i, x)) $ zip [0 ..] $ V.toList sol
  where
    initState =
      RankState
        { stateCounter = 0,
          stateBinMap = mempty,
          stateConstraints = mempty,
          stateObjSet = mempty
        }
