{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The Algebraic Environment, which is in principle
--   maintained during program traversal, is used to
--   solve symbolically algebraic inequations.
module Futhark.SoP.Monad
  ( Nameable (..),
    mkNameM,
    RangeEnv,
    EquivEnv,
    UntransEnv (..),
    AlgEnv (..),
    type (>=),
    type (==),
    addUntrans,
    transClosInRanges,
    lookupUntransPE,
    lookupUntransSym,
    lookupRange,
    addRange,
    SoPMT,
    SoPM,
    lookupSoP,
    runSoPMT,
    runSoPMT_,
    runSoPM,
    runSoPM_,
    evalSoPMT,
    evalSoPMT_,
    evalSoPM,
    evalSoPM_,
    MonadSoP (..),
  )
where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Futhark.Analysis.PrimExp
import Futhark.FreshNames
import Futhark.MonadFreshNames
import Futhark.SoP.SoP
import Futhark.Util.Pretty
import GHC.TypeLits (Natural)
import Language.Futhark.Syntax hiding (Range)

--------------------------------------------------------------------------------
-- Names; probably will remove in the end.
--------------------------------------------------------------------------------

-- | Types which can use a fresh source to generate
--   unique names.
class Nameable u where
  mkName :: VNameSource -> (u, VNameSource)

instance Nameable String where
  mkName (VNameSource i) = ("x" <> show i, VNameSource $ i + 1)

instance Nameable VName where
  mkName (VNameSource i) = (VName "x" i, VNameSource $ i + 1)

instance Nameable Name where
  mkName = mkName

mkNameM :: (Nameable u, MonadFreshNames m) => m u
mkNameM = modifyNameSource mkName

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

class
  ( Ord u,
    Nameable u,
    Show u, -- To be removed
    Pretty u, -- To be removed
    MonadFreshNames m
  ) =>
  MonadSoP u m
    | m -> u
  where
  getUntrans :: m (UntransEnv u)
  getRanges :: m (RangeEnv u)
  getEquivs :: m (EquivEnv u)
  modifyEnv :: (AlgEnv u -> AlgEnv u) -> m ()

-- | The algebraic monad; consists of a an algebraic
--   environment along with a fresh variable source.
newtype SoPMT u m a = SoPMT (StateT (AlgEnv u) m a)
  deriving
    ( Functor,
      Applicative,
      Monad
    )

instance MonadTrans (SoPMT u) where
  lift = SoPMT . lift

instance MonadFreshNames m => MonadFreshNames (SoPMT u m) where
  getNameSource = lift getNameSource
  putNameSource = lift . putNameSource

instance (MonadFreshNames m) => MonadFreshNames (StateT (AlgEnv u) m) where
  getNameSource = lift getNameSource
  putNameSource = lift . putNameSource

instance MonadReader r m => MonadReader r (SoPMT u m) where
  ask = SoPMT $ lift ask
  local f (SoPMT m) =
    SoPMT $ do
      env <- get
      (a, env') <- lift $ local f $ runStateT m env
      put env'
      pure a

instance MonadState s m => MonadState s (SoPMT u m) where
  get = SoPMT $ lift get
  put = SoPMT . lift . put

type SoPM u = SoPMT u (State VNameSource)

runSoPMT :: MonadFreshNames m => AlgEnv u -> SoPMT u m a -> m (a, AlgEnv u)
runSoPMT env (SoPMT sm) = runStateT sm env

runSoPMT_ :: (Ord u, MonadFreshNames m) => SoPMT u m a -> m (a, AlgEnv u)
runSoPMT_ = runSoPMT mempty

runSoPM :: Ord u => AlgEnv u -> SoPM u a -> (a, AlgEnv u)
runSoPM env = flip evalState mempty . runSoPMT env

runSoPM_ :: Ord u => SoPM u a -> (a, AlgEnv u)
runSoPM_ = runSoPM mempty

evalSoPMT :: MonadFreshNames m => AlgEnv u -> SoPMT u m a -> m a
evalSoPMT env m = fst <$> runSoPMT env m

evalSoPMT_ :: (Ord u, MonadFreshNames m) => SoPMT u m a -> m a
evalSoPMT_ = evalSoPMT mempty

evalSoPM :: Ord u => AlgEnv u -> SoPM u a -> a
evalSoPM env = fst . runSoPM env

evalSoPM_ :: Ord u => SoPM u a -> a
evalSoPM_ = evalSoPM mempty

instance
  ( Ord u,
    Nameable u,
    Show u,
    Pretty u,
    MonadFreshNames m
  ) =>
  MonadSoP u (SoPMT u m)
  where
  getUntrans = SoPMT $ gets untrans

  getRanges = SoPMT $ gets ranges

  getEquivs = SoPMT $ gets equivs

  modifyEnv f = SoPMT $ modify f

-- \| Insert a symbol equal to an untranslatable 'PrimExp'.
addUntrans :: MonadSoP u m => u -> PrimExp u -> m ()
addUntrans sym pe =
  modifyEnv $ \env ->
    env
      { untrans =
          (untrans env)
            { dir = M.insert sym pe (dir (untrans env)),
              inv = M.insert pe sym (inv (untrans env))
            }
      }

-- \| Look-up the sum-of-products representation of a symbol.
lookupSoP :: MonadSoP u m => u -> m (Maybe (SoP u))
lookupSoP x = (M.!? x) <$> getEquivs

-- \| Look-up the symbol for a 'PrimExp'. If no symbol is bound
--    to the expression, bind a new one.
lookupUntransPE :: MonadSoP u m => PrimExp u -> m u
lookupUntransPE pe = do
  inv_map <- inv <$> getUntrans
  case inv_map M.!? pe of
    Nothing -> do
      x <- mkNameM
      addUntrans x pe
      pure x
    Just x -> pure x

-- \| Look-up the untranslatable 'PrimExp' bound to the given symbol.
lookupUntransSym :: MonadSoP u m => u -> m (Maybe (PrimExp u))
lookupUntransSym sym = ((M.!? sym) . dir) <$> getUntrans

-- \| Look-up the range of a symbol. If no such range exists,
--    return the empty range (and add it to the environment).
lookupRange :: MonadSoP u m => u -> m (Range u)
lookupRange sym = do
  mr <- (M.!? sym) <$> getRanges
  case mr of
    Nothing -> do
      let r = Range mempty 1 mempty
      addRange sym r
      pure r
    Just r
      | rangeMult r <= 0 -> error "Non-positive constant encountered in range."
      | otherwise -> pure r

-- \| Add range information for a symbol; augments the existing
--   range.
addRange :: MonadSoP u m => u -> Range u -> m ()
addRange sym r =
  modifyEnv $ \env ->
    env {ranges = M.insertWith (<>) sym r (ranges env)}

--------------------------------------------------------------------------------
-- Environment
--------------------------------------------------------------------------------

-- | A type label to indicate @a >= 0@.
type a >= (b :: Natural) = a

-- | A type label to indicate @a = 0@.
type a == (b :: Natural) = a

-- | The environment of untranslatable 'PrimeExp's.  It maps both
--   ways:
--
--   1. A fresh symbol is generated and mapped to the
--      corresponding 'PrimeExp' @pe@ in 'dir'.
--   2. The target @pe@ is mapped backed to the corresponding symbol in 'inv'.
data UntransEnv u = Unknowns
  { dir :: Map u (PrimExp u),
    inv :: Map (PrimExp u) u
  }
  deriving (Eq, Show, Ord)

instance Ord u => Semigroup (UntransEnv u) where
  Unknowns d1 i1 <> Unknowns d2 i2 = Unknowns (d1 <> d2) (i1 <> i2)

instance Ord u => Monoid (UntransEnv u) where
  mempty = Unknowns mempty mempty

-- | The equivalence environment binds a variable name to
--   its equivalent 'SoP' representation.
type EquivEnv u = Map u (SoP u)

-- | The range environment binds a variable name to a range.
type RangeEnv u = Map u (Range u)

instance Pretty u => Pretty (RangeEnv u) where
  pretty = pretty . M.toList

-- | The main algebraic environment.
data AlgEnv u = AlgEnv
  { -- | Binds untranslatable PrimExps to fresh symbols.
    untrans :: UntransEnv u,
    -- | Binds symbols to their sum-of-product representation..
    equivs :: EquivEnv u,
    -- | Binds symbols to ranges (in sum-of-product form).
    ranges :: RangeEnv u
  }
  deriving (Ord, Show, Eq)

instance Ord u => Semigroup (AlgEnv u) where
  AlgEnv u1 s1 r1 <> AlgEnv u2 s2 r2 =
    AlgEnv (u1 <> u2) (s1 <> s2) (r1 <> r2)

instance Ord u => Monoid (AlgEnv u) where
  mempty = AlgEnv mempty mempty mempty

transClosInRanges :: (Ord u) => RangeEnv u -> Set u -> Set u
transClosInRanges rs syms =
  transClosHelper rs syms S.empty syms
  where
    transClosHelper rs' clos_syms seen active
      | S.null active = clos_syms
      | (sym, active') <- S.deleteFindMin active,
        seen' <- S.insert sym seen =
          case M.lookup sym rs' of
            Nothing ->
              transClosHelper rs' clos_syms seen' active'
            Just range ->
              let new_syms = free range S.\\ seen
                  clos_syms' = S.union clos_syms new_syms
                  active'' = S.union new_syms active'
               in transClosHelper rs' clos_syms' seen' active''