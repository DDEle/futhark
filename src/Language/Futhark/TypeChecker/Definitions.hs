module Language.Futhark.TypeChecker.Definitions (checkFunDef) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Bitraversable
import Data.Char (isAscii)
import Data.Either
import Data.List (delete, find, genericLength, partition)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Set qualified as S
import Debug.Trace
import Futhark.MonadFreshNames
import Futhark.Solve.LP (LSum (..), LinearProg (..), OptType (..))
import Futhark.Solve.LP qualified as LP
import Futhark.Util (mapAccumLM, nubOrd, topologicalSort)
import Futhark.Util.Pretty hiding (space)
import Language.Futhark
import Language.Futhark.Primitive (intByteSize)
import Language.Futhark.Traversals
import Language.Futhark.TypeChecker.Constraint
import Language.Futhark.TypeChecker.Consumption qualified as Consumption
import Language.Futhark.TypeChecker.Match
import Language.Futhark.TypeChecker.Monad hiding (BoundV, TypeState (..), newName)
import Language.Futhark.TypeChecker.Monad qualified as TypeM
import Language.Futhark.TypeChecker.Rank (solveRanks)
import Language.Futhark.TypeChecker.Types
import Prelude hiding (mod)

incCounter :: ConstrainM Int
incCounter = do
  s <- get
  put s {stateCounter = stateCounter s + 1}
  pure $ stateCounter s

data ConstrainEnv = ConstrainEnv {}

data ConstrainState = ConstrainState
  { stateConstraints :: Constraints,
    stateCounter :: !Int,
    stateWarnings :: Warnings,
    stateNameSource :: VNameSource
  }

newtype ConstrainM a
  = ConstrainM
      ( ReaderT
          ConstrainEnv
          (State ConstrainState)
          a
      )
  deriving
    ( Monad,
      Functor,
      Applicative,
      MonadReader ConstrainEnv,
      MonadState ConstrainState
    )

instance MonadFreshNames ConstrainM where
  getNameSource = gets stateNameSource
  putNameSource vns = modify $ \env -> env {stateNameSource = vns}

runConstrainM :: ConstrainM a -> TypeM a
runConstrainM (ConstrainM m) = do
  src <- gets TypeM.stateNameSource
  let initial_cenv =
        ConstrainEnv {}
      initial_state =
        ConstrainState
          { stateConstraints = mempty,
            stateCounter = 0,
            stateNameSource = src
          }
      (a, ConstrainState {stateNameSource}) =
        runState (runReaderT m initial_cenv) initial_state
  modify $ \s -> s {TypeM.stateNameSource = stateNameSource}
  pure a

newTypeVar :: (Monoid als) => SrcLoc -> Name -> ConstrainM (TypeBase dim als)
newTypeVar loc desc = do
  i <- incCounter
  v <- newName $ VName (mkTypeVarName desc i) 0
  pure $ Scalar $ TypeVar mempty (qualName v) []

addConstraints :: Constraints -> ConstrainM ()
addConstraints cs = modify $ \env ->
  env
    { stateConstraints =
        stateConstraints env ++ cs
    }

addConstraint :: Constraint -> ConstrainM ()
addConstraint c = addConstraints [c]

-- | Check and bind type and value parameters.
-- bindingParams ::
--  [UncheckedTypeParam] ->
--  [UncheckedPat ParamType] ->
--  ([TypeParam] -> [Pat ParamType] -> ConstrainM a) ->
--  ConstrainM a
checkFunDef ::
  ( Name,
    Maybe UncheckedTypeExp,
    [UncheckedTypeParam],
    [UncheckedPat ParamType],
    UncheckedExp,
    SrcLoc
  ) ->
  TypeM
    ( VName,
      [TypeParam],
      [Pat ParamType],
      Maybe (TypeExp Info VName),
      ResRetType,
      Exp
    )
checkFunDef (fname, maybe_retdecl, tparams, params, body, loc) =
  runConstrainM $ do
    fname' <- newName $ VName fname 0
    -- tparams' <- mapM checkTParam tparams
    -- params' <- mapM checkPat params
    body' <- checkExp body
    let ret = toResRet mempty $ RetType mempty $ typeOf body'
    -- pure (fname', tparams', params', Nothing, ret, body')
    pure (fname', mempty, mempty, Nothing, ret, body')

checkExp :: UncheckedExp -> ConstrainM Exp
checkExp e = do
  e' <- constrainExp e
  cs <- gets stateConstraints
  ranks <- solveRanks <$> gets stateConstraints
  traceM $ unlines ["cs: " <> show cs, "ranks: " <> show ranks]
  pure e'

constrainExp :: UncheckedExp -> ConstrainM Exp
constrainExp (Literal val loc) =
  pure $ Literal val loc
constrainExp (IntLit val NoInfo loc) = do
  t <- newTypeVar loc "t"
  addConstraint $ Overloaded t anyNumberType
  pure $ IntLit val (Info t) loc
constrainExp e = error $ unlines [prettyString e, show e]

-- checkTypeExp :: TypeExp NoInfo Name ->
-- ConstrainM (TypeExp Info VName, [VName], ResRetType, Liftedness)
-- checkTypeExp (TEVar (QualName [] n) loc) =
--
--
-- evalTypeExp (TEVar name loc) = do
--  (name', ps, t, l) <- lookupType loc name
--  t' <- renameRetType $ toResRet Nonunique t
--  case ps of
--    [] -> pure (TEVar name' loc, [], t', l)
--    _ ->
--      typeError loc mempty $
--        "Type constructor"
--          <+> dquotes (hsep (pretty name : map pretty ps))
--          <+> "used without any arguments."
--
-- lookupType :: SrcLoc -> QualName Name -> m (QualName VName, [TypeParam], StructRetType, Liftedness)
-- lookupType ::
--  lookupType loc qn = do
--    outer_env <- asks termOuterEnv
--    (scope, qn'@(QualName qs name)) <- checkQualNameWithEnv Type qn loc
--    case M.lookup name $ scopeTypeTable scope of
--      Nothing -> unknownType loc qn
--      Just (TypeAbbr l ps (RetType dims def)) ->
--        pure
--          ( qn',
--            ps,
--            RetType dims $ qualifyTypeVars outer_env (map typeParamName ps) qs def,
--            l
--          )

checkBody = checkExp

checkPat = undefined

-- checkPat :: UncheckedPat ParamType -> ConstrainM (Pat ParamType)
-- checkPat (Id n NoInfo loc) = do
-- vn <- newID n
-- pure $ Id vn (

checkTParam = undefined

-------------------------------------------------------------
