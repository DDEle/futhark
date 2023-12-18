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
import Data.Map.Strict (Map)
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

type Scheme = ([TypeParam], StructType)

incCounter :: ConstrainM Int
incCounter = do
  s <- get
  put s {stateCounter = stateCounter s + 1}
  pure $ stateCounter s

data ConstrainEnv = ConstrainEnv
  { envSchemeMap :: Map VName Scheme
  }

extendSEnv :: VName -> Scheme -> ConstrainM a -> ConstrainM a
extendSEnv x s =
  local $ \env -> env {envSchemeMap = M.insert x s $ envSchemeMap env}

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

newTypeVar :: (Monoid als) => Name -> ConstrainM (TypeBase dim als)
newTypeVar desc = do
  i <- incCounter
  v <- newName $ VName (mkTypeVarName desc i) 0
  pure $ Scalar $ TypeVar mempty (qualName v) []

newShapeVar :: Name -> ConstrainM (VName)
newShapeVar desc = do
  i <- incCounter
  newName $ VName (mkTypeVarName desc i) 0

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
  traceM $ unlines ["e: " <> prettyString e, "cs: " <> show cs, "ranks: " <> show ranks]
  pure e'

checkPat :: UncheckedPat ParamType -> ConstrainM (Pat ParamType)
checkPat (Id n NoInfo loc) = do
  vn <- newName $ VName n 0
  t <- newTypeVar "t"
  pure $ Id vn (Info t) loc

checkTParam = undefined

constrainExp :: UncheckedExp -> ConstrainM Exp
constrainExp (Literal val loc) =
  pure $ Literal val loc
constrainExp (IntLit val NoInfo loc) = do
  t <- newTypeVar "t"
  addConstraint $ Overloaded t anyNumberType
  pure $ IntLit val (Info t) loc
constrainExp (Var (QualName [] x) NoInfo loc) = do
  x' <- newName $ VName x 0
  t <- newTypeVar "t"
  pure $ Var (QualName [] x') (Info t) loc
constrainExp (AppExp (Apply f args loc) NoInfo) = do
  f' <- constrainExp f
  args' <- mapM (constrainExp . snd) args
  constrainApply f' args'
constrainExp (AppExp (BinOp (op@(QualName [] "+"), oploc) NoInfo (x, _) (y, _) loc) NoInfo) = do
  x' <- constrainExp x
  y' <- constrainExp y
  t <- newTypeVar "t"
  op' <- QualName [] <$> (newName $ VName "+" 0)
  addConstraint $ Overloaded t anyNumberType
  let f_type = foldFunType [toParam Observe t, toParam Observe t] (RetType mempty $ toRes Nonunique t)
      f = Var op' (Info f_type) oploc
  res <- constrainApply f $ NE.fromList [x', y']
  pure (AppExp (BinOp (op', oploc) (Info f_type) (x', Info Nothing) (y', Info Nothing) loc) (Info $ AppRes (typeOf res) mempty))
constrainExp (Parens e loc) = do
  e' <- constrainExp e
  pure $ Parens e' loc
constrainExp (Lambda params body _ NoInfo loc) = do
  params' <- mapM checkPat params
  body' <- constrainExp body
  let rt = RetType mempty $ toRes Nonunique (typeOf body')
  pure $ Lambda params' body' Nothing (Info rt) loc
-- constrain (Lam (x, _) e _) = do
--   x_t <- newTVar
--   (e', e_t) <-
--     extendSEnv x x_t $
--       constrain e
--   pure (Lam (x, Id $ Type x_t) e' (Id $ Type (x_t :-> e_t)), x_t :-> e_t)

constrainExp e = error $ unlines [prettyString e, show e]

constrainApply :: Exp -> NE.NonEmpty Exp -> ConstrainM Exp
constrainApply f args = foldM constrainOneApply f args

constrainOneApply :: Exp -> Exp -> ConstrainM Exp
constrainOneApply f arg = do
  let f_e = frameOf arg
  (t1, t2) <-
    case f_t of
      Scalar (Arrow _ _ _ t1 (RetType _ t2)) ->
        pure (t1, toStruct t2)
      Scalar (TypeVar u _ _) -> do
        t1 <- newTypeVar "t1"
        t2 <- newTypeVar "t2"
        addConstraint $
          f_t
            :== Scalar (Arrow mempty Unnamed Observe t1 $ RetType [] t2)
        pure (t1, toStruct t2)
      _ -> error $ unlines [prettyString f_t, show f_t]
  s_rep <- newShapeVar "Rep"
  s_map <- newShapeVar "Map"
  let rt = distribute $ arrayOf (SVar s_map) t2
  addConstraints
    [ distribute (arrayOf (SVar s_rep <> f_e) (typeOf arg)) :== distribute (arrayOf (SVar s_map <> f_f) t1),
      OneIsZero s_rep s_map
    ]
  let am =
        AutoMap
          { autoRep = SVar s_rep,
            autoMap = SVar s_map,
            autoFrame = SVar s_map <> f_f
          }
      farg = mkApply f [(mempty, Nothing, am, arg)] (AppRes rt mempty)
  pure farg
  where
    f_f = frameOf f
    f_t = typeOf f

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

-------------------------------------------------------------
