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
import Futhark.MonadFreshNames
import Futhark.Solve.LP (LSum (..), LinearProg (..), OptType (..))
import Futhark.Solve.LP qualified as LP
import Futhark.Util (mapAccumLM, nubOrd, topologicalSort)
import Futhark.Util.Pretty hiding (space)
import Language.Futhark
import Language.Futhark.Primitive (intByteSize)
import Language.Futhark.Traversals
import Language.Futhark.TypeChecker.Consumption qualified as Consumption
import Language.Futhark.TypeChecker.Match
import Language.Futhark.TypeChecker.Monad hiding (BoundV, TypeState (..), newName)
import Language.Futhark.TypeChecker.Monad qualified as TypeM
import Language.Futhark.TypeChecker.Types
import Prelude hiding (mod)

data TermEnv = TermEnv {}

data Constraint
  = (:==) StructType StructType
  | OneIsZero VName VName
  | Overloaded StructType [PrimType]
  deriving (Show, Eq)

type Constraints = [Constraint]

incCounter :: TermTypeM Int
incCounter = do
  s <- get
  put s {stateCounter = stateCounter s + 1}
  pure $ stateCounter s

data TermTypeState = TermTypeState
  { stateConstraints :: Constraints,
    stateCounter :: !Int,
    stateWarnings :: Warnings,
    stateNameSource :: VNameSource
  }

newtype TermTypeM a
  = TermTypeM
      ( ReaderT
          TermEnv
          (StateT TermTypeState (Except (Warnings, TypeError)))
          a
      )
  deriving
    ( Monad,
      Functor,
      Applicative,
      MonadReader TermEnv,
      MonadState TermTypeState
    )

instance MonadFreshNames TermTypeM where
  getNameSource = gets stateNameSource
  putNameSource vns = modify $ \env -> env {stateNameSource = vns}

instance MonadError TypeError TermTypeM where
  throwError e = TermTypeM $ do
    ws <- gets stateWarnings
    throwError (ws, e)

  catchError (TermTypeM m) f =
    TermTypeM $ m `catchError` f'
    where
      f' (_, e) = let TermTypeM m' = f e in m'

runTermTypeM :: TermTypeM a -> TypeM a
runTermTypeM (TermTypeM m) = do
  name <- askImportName
  outer_env <- askEnv
  src <- gets TypeM.stateNameSource
  let initial_tenv =
        TermEnv {}
      initial_state =
        TermTypeState
          { stateConstraints = mempty,
            stateCounter = 0,
            stateWarnings = mempty,
            stateNameSource = src
          }
  case runExcept (runStateT (runReaderT m initial_tenv) initial_state) of
    Left (ws, e) -> do
      warnings ws
      throwError e
    Right (a, TermTypeState {stateNameSource, stateWarnings}) -> do
      warnings stateWarnings
      modify $ \s -> s {TypeM.stateNameSource = stateNameSource}
      pure a

newTypeVar :: (Monoid als) => SrcLoc -> Name -> TermTypeM (TypeBase dim als)
newTypeVar loc desc = do
  i <- incCounter
  v <- newName $ VName (mkTypeVarName desc i) 0
  pure $ Scalar $ TypeVar mempty (qualName v) []

addConstraints :: Constraints -> TermTypeM ()
addConstraints cs = modify $ \env ->
  env
    { stateConstraints =
        stateConstraints env ++ cs
    }

addConstraint :: Constraint -> TermTypeM ()
addConstraint c = addConstraints [c]

-- | Check and bind type and value parameters.
-- bindingParams ::
--  [UncheckedTypeParam] ->
--  [UncheckedPat ParamType] ->
--  ([TypeParam] -> [Pat ParamType] -> TermTypeM a) ->
--  TermTypeM a
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
  runTermTypeM $ do
    fname' <- newName $ VName fname 0
    tparams' <- mapM checkTParam tparams
    params' <- mapM checkPat params
    body' <- checkExp body
    let ret = toResRet mempty $ RetType mempty $ typeOf body'
    pure (fname', tparams', params', Nothing, ret, body')

checkExp :: UncheckedExp -> TermTypeM Exp
checkExp e = do
  constrainExp e
  undefined

constrainExp :: UncheckedExp -> TermTypeM Exp
constrainExp (Literal val loc) =
  pure $ Literal val loc
constrainExp (IntLit val NoInfo loc) = do
  t <- newTypeVar loc "t"
  addConstraint $ Overloaded t anyNumberType
  pure $ IntLit val (Info t) loc
constrainExp e = error $ unlines [prettyString e, show e]

-- checkTypeExp :: TypeExp NoInfo Name ->
-- TermTypeM (TypeExp Info VName, [VName], ResRetType, Liftedness)
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

-- checkPat :: UncheckedPat ParamType -> TermTypeM (Pat ParamType)
-- checkPat (Id n NoInfo loc) = do
-- vn <- newID n
-- pure $ Id vn (

checkTParam = undefined

----------------------------

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

rankProg ::
  (MonadFreshNames m) =>
  forall b.
  (Num b, Eq b) =>
  Constraints ->
  m (LinearProg VName b)
rankProg cs = undefined
  where
    convertConstraint (t1 :== t2) =
      pure [mkRank t1 LP.== mkRank t2]
    convertConstraint (OneIsZero s1 s2) = do
      b1 <- newName s1
      b2 <- newName s2
      pure $
        LP.or
          b1
          b2
          (LP.var s1 LP.== LP.constant 0)
          (LP.var s2 LP.== LP.constant 0)
    convertConstraint (Overloaded t _) =
      pure [mkRank t LP.== LP.constant 0]
