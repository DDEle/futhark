module Futhark.Analysis.View (mkIndexFnProg) where

import Data.List qualified as L
import Data.List.NonEmpty()
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Futhark.Analysis.View.Representation
import Futhark.Analysis.View.Refine
import Futhark.Analysis.View.Substitution
import Futhark.MonadFreshNames
import Futhark.Util.Pretty
import Futhark.SoP.SoP qualified as SoP
import Language.Futhark.Semantic
import Language.Futhark qualified as E
import qualified Data.Map as M
import Debug.Trace (traceM, trace)
import qualified Data.Set as S
import Futhark.Analysis.View.Rules
import Control.Monad.RWS.Strict hiding (Sum)


--------------------------------------------------------------
tracePrettyM :: (Applicative f, Pretty a) => a -> f ()
tracePrettyM = traceM . prettyString
--------------------------------------------------------------

--------------------------------------------------------------
-- Extracting information from E.Exp.
--------------------------------------------------------------
getFun :: E.Exp -> Maybe String
getFun (E.Var (E.QualName [] vn) _ _) = Just $ E.baseString vn
getFun _ = Nothing

getSize :: E.Exp -> Maybe Term
getSize (E.Var _ (E.Info {E.unInfo = E.Scalar _}) _) =
  Nothing
getSize (E.Var _ (E.Info {E.unInfo = E.Array _ _ shape _}) _)
  | dim:_ <- E.shapeDims shape =
    Just $ convertSize dim
getSize (E.ArrayLit [] (E.Info {E.unInfo = E.Array _ _ shape _}) _)
  | dim:_ <- E.shapeDims shape =
    Just $ convertSize dim
getSize e = error $ "getSize: " <> prettyString e <> "\n" <> show e

-- Used for converting sizes of function arguments.
convertSize :: E.Exp -> Term
convertSize (E.Var (E.QualName _ x) _ _) = Var x
convertSize (E.Parens e _) = convertSize e
convertSize (E.Attr _ e _) = convertSize e
convertSize (E.IntLit x _ _) = SoP2 $ SoP.int2SoP x
convertSize e = error ("convertSize not implemented for: " <> show e)

-- Strip unused information.
getArgs :: NE.NonEmpty (a, E.Exp) -> [E.Exp]
getArgs = map (stripExp . snd) . NE.toList
  where
    stripExp x = fromMaybe x (E.stripExp x)

--------------------------------------------------------------
-- Refine source program
--------------------------------------------------------------

-- mkIndexFnProg :: VNameSource -> [E.Dec] -> IndexFns
-- mkIndexFnProg vns prog = tracePretty $ execIndexFnM (mkIndexFnDecs prog) vns
mkIndexFnProg :: VNameSource -> Imports -> IndexFns
mkIndexFnProg vns prog = execIndexFnM (mkIndexFnImports prog) vns

mkIndexFnImports :: [(ImportName, FileModule)] -> IndexFnM ()
mkIndexFnImports = mapM_ (mkIndexFnDecs . E.progDecs . fileProg . snd)
-- A program is a list of declarations (DecBase); functions are value bindings
-- (ValBind). Everything is in an AppExp.

mkIndexFnDecs :: [E.Dec] -> IndexFnM ()
mkIndexFnDecs [] = pure ()
mkIndexFnDecs (E.ValDec vb : rest) = do
  mkIndexFnValBind vb
  mkIndexFnDecs rest
mkIndexFnDecs (_ : ds) = mkIndexFnDecs ds

mkIndexFnValBind :: E.ValBind -> IndexFnM ()
mkIndexFnValBind (E.ValBind _ vn ret _ _ params body _ _ _) =
  -- mapM_ paramRefs params
  -- forwards body
  case ret of
    Just (E.TERefine _t _goal _) -> do
      -- We don't really care about the goal right now, as
      -- we just want to express the value binding as an index function.
      traceM ("\n====\nmkIndexFnValBind: " <> prettyString vn)
      traceM ("\nTo prove:\n--------\n" <> prettyString ret)
      traceM ("\nWith params\n-----------\n" <> prettyString params)
      traceM ("\nFor body\n--------\n" <> prettyString body <> "\n====\n")
      forwards body
      pure ()
    _ -> pure ()


forwards :: E.Exp -> IndexFnM ()
forwards (E.AppExp (E.LetPat _ p e body _) _)
  | (E.Named x, _, _) <- E.patternParam p = do
    traceM (prettyString p <> " = " <> prettyString e)
    newIndexFn <- forward e
    tracePrettyM newIndexFn
    traceM "🪨 refining"
    newIndexFn' <- rewrite newIndexFn >>= refineIndexFn >>= rewrite
    tracePrettyM newIndexFn'
    traceM "\n"
    insertIndexFn x newIndexFn'
    forwards body
    pure ()
forwards _ = pure ()


forward :: E.Exp -> IndexFnM IndexFn
forward (E.Parens e _) = forward e
forward (E.Attr _ e _) = forward e
-- Leaves.
forward (E.Literal (E.BoolValue x) _) =
  normalise . toScalarIndexFn $ Bool x
forward (E.IntLit x _ _) =
  normalise . toScalarIndexFn . SoP2 $ SoP.int2SoP x
forward (E.Negate (E.IntLit x _ _) _) =
  normalise . toScalarIndexFn . SoP2 $ SoP.negSoP $ SoP.int2SoP x
forward e@(E.Var (E.QualName _ vn) _ _) = do
  indexfns <- gets indexfns
  case M.lookup vn indexfns of
    Just v@(IndexFn _ _) -> do
      traceM ("🪸 substituting " <> prettyString e <> " for " <> prettyString v)
      pure v
    _ ->
      case getSize e of
        Just sz -> do
          -- Canonical array representation.
          i <- newNameFromString "i"
          normalise $ IndexFn (Forall i (Iota sz))
                           (toCases $ Idx (Var vn) (termToSoP (Var i)))
        Nothing ->
          -- Canonical scalar representation.
          normalise $ IndexFn Empty (toCases $ Var vn)
-- Nodes.
forward (E.AppExp (E.Index xs' slice _) _)
  | [E.DimFix idx'] <- slice = do -- XXX support only simple indexing for now
      IndexFn iter_idx idx <- forward idx'
      IndexFn iter_xs xs <- forward xs'
      debugM ("index " <> prettyString xs' <> " by " <> prettyString idx')
      case iteratorName iter_xs of
        Just j -> do
          -- This case can be funky. Treating `a[i]` inside the map lambda
          --   let a = scan (+) 0i64 x
          --   let b = map (\i -> a[i]) (iota n)
          -- yields:
          --   index a by i
          --   a: ∀i₆₁₀₂ ∈ iota n₆₀₆₈ .
          --     | True => Σj₆₁₀₄∈[0, ..., i₆₁₀₂] ((x₆₀₇₀)[j₆₁₀₄])
          --   i: .
          --     | True => i₆₀₉₃
          --   sub i_6102 for .
          --     | True => i₆₀₉₃
          --    in .
          --     | True => Σj₆₁₀₄∈[0, ..., i₆₁₀₂] ((x₆₀₇₀)[j₆₁₀₄])
          --   sub result: .
          --     | True => Σj₆₁₀₄∈[0, ..., i₆₀₉₃] ((x₆₀₇₀)[j₆₁₀₄])
          -- So the result is a scalar because i₆₀₉₃ is a scalar in this context,
          -- because we are inside the body of the map lambda.
          -- (I think this is correct; i₆₀₉₃ is a program variable like x₆₀₇₀.)
          rewrite $ sub j (IndexFn iter_idx idx) (IndexFn iter_idx xs)
        Nothing ->
          error "indexing into a scalar"
forward (E.Not e _) = do
  IndexFn it e' <- forward e
  rewrite $ IndexFn it $ cmapValues Not e'
forward (E.ArrayLit _es _ _) =
  error "forward on array literal"
forward (E.AppExp (E.LetPat _ (E.Id vn _ _) x y _) _) = do
  x' <- forward x
  y' <- forward y
  rewrite $ sub vn x' y'
forward (E.AppExp (E.BinOp (op, _) _ (x', _) (y', _) _) _)
  | E.baseTag (E.qualLeaf op) <= E.maxIntrinsicTag,
    name <- E.baseString $ E.qualLeaf op,
    Just bop <- L.find ((name ==) . prettyString) [minBound .. maxBound :: E.BinOp] = do
      IndexFn iter_x x <- forward x'
      vy <- forward y'
      a <- newNameFromString "a"
      b <- newNameFromString "b"
      let doOp op = rewrite $
                          sub b vy $
                            sub a (IndexFn iter_x x) $
                              IndexFn iter_x (toCases $ op (Var a) (Var b))
      case bop of
        E.Plus -> doOp (~+~)
        E.Times -> doOp (~*~)
        E.Minus -> doOp (~-~)
        E.Equal -> doOp (:==)
        E.Less -> doOp (:<)
        E.Greater -> doOp (:>)
        E.Leq -> doOp (:<=)
        E.LogAnd -> doOp (:&&)
        E.LogOr -> doOp (:||)
        _ -> error ("forward not implemented for bin op: " <> show bop)
forward (E.AppExp (E.If c t f _) _) = do
  IndexFn iter_c c' <- forward c
  vt <- forward t
  vf <- forward f
  -- Negating `c` means negating the case _values_ of c, keeping the
  -- conditions of any nested if-statements (case conditions) untouched.
  cond <- newNameFromString "cond"
  t_branch <- newNameFromString "t_branch"
  f_branch <- newNameFromString "f_branch"
  let y = IndexFn iter_c (Cases . NE.fromList $ [(Var cond, Var t_branch),
                                              (Not $ Var cond, Var f_branch)])
  rewrite $
    sub f_branch vf $
      sub t_branch vt $
        sub cond (IndexFn iter_c c') y
forward (E.AppExp (E.Apply f args _) _)
  | Just fname <- getFun f,
    "map" `L.isPrefixOf` fname,
    E.Lambda params body _ _ _ : args' <- getArgs args = do
      xss <- mapM forward args'
      let IndexFn iter_y _ = head xss
      -- TODO use iter_body; likely needed for nested maps?
      IndexFn iter_body cases_body <- forward body
      unless (iter_body == iter_y || iter_body == Empty)
             (error $ "map: got incompatible iterator from map lambda body: "
                      <> show iter_body)
      debugM ("map args " <> prettyString xss)
      debugM ("map body " <> prettyString (IndexFn iter_body cases_body))
      -- Make susbtitutions from function arguments to array names.
      -- TODO `map E.patNames params` is a [Set], I assume because we might have
      --   map (\(x, y) -> ...) xys
      -- meaning x needs to be substituted by x[i].0
      let paramNames = mconcat $ map (S.toList . E.patNames) params
      --               ^ XXX mconcat is wrong, see above
      let s y (paramName, paramIndexFn) = sub paramName paramIndexFn y
      rewrite $
        foldl s (IndexFn iter_y cases_body) (zip paramNames xss)
  | Just "scan" <- getFun f,
    [E.OpSection (E.QualName [] vn) _ _, _ne, xs'] <- getArgs args = do
      IndexFn iter_xs xs <- forward xs'
      let Just i = iteratorName iter_xs
      -- TODO should verify that _ne matches op
      op <-
        case E.baseString vn of
          "+" -> pure (~+~)
          "-" -> pure (~-~)
          "*" -> pure (~*~)
          _ -> error ("scan not implemented for bin op: " <> show vn)
      let base_case = Var i :== SoP2 (SoP.int2SoP 0)
      x <- newNameFromString "x"
      let y = IndexFn
                iter_xs
                (Cases . NE.fromList $
                  [(base_case, Var x), (Not base_case, Recurrence `op` Var x)])
      rewrite $ sub x (IndexFn iter_xs xs) y
  | Just "scatter" <- getFun f,
    [dest_arg, inds_arg, vals_arg] <- getArgs args = do
      -- Scatter in-bounds-monotonic indices.
      --
      -- b has at least size m
      -- b[k-1] <= b[k] for all k     (e.g., sum of positive ints; can be checked from SoP?)
      -- inds = ∀k ∈ [1, ..., m] .
      --     | c1 => OOB              (c1 may depend on i)
      --     | c2 => b[k-1]           (c2 may depend on i)
      -- dest has size b[m-1]
      -- y = scatter dest inds vals
      -- ___________________________________________________
      -- y = ∀i ∈ ⋃k=1,...,m ([b[k-1], ..., b[k]]) .
      --     | i == inds[k] => vals[k]
      --     | i /= inds[k] => dest[i]
      --
      -- From type checking, we have:
      -- scatter : (dest : [n]t) -> (inds : [m]i64) -> (vals : [m]t) : [n]t
      -- * inds and vals are same size
      -- * dest and result are same size
      inds <- forward inds_arg
      -- get size m
      -- extract b from inds
      -- check monotonicity on b
      -- check that cases match pattern with OOB < 0 or OOB > b[m-1]
      vals <- forward vals_arg
      -- check that iterator matches that of inds
      dest <- forward dest_arg
      -- check dest has size b[m-1]
      undefined
  | Just "iota" <- getFun f,
    [n] <- getArgs args = do
      indexfn <- forward n
      i <- newNameFromString "i"
      case indexfn of
        IndexFn Empty (Cases ((Bool True, m) NE.:| [])) ->
              rewrite $ IndexFn (Forall i (Iota m)) (toCases $ Var i)
        _ -> undefined -- TODO We've no way to express this yet.
                       -- Have talked with Cosmin about an "outer if" before.
  | Just "replicate" <- getFun f,
    [n, x] <- getArgs args = do
      n' <- forward n
      x' <- forward x
      i <- newNameFromString "i"
      case (n', x') of
        (IndexFn Empty (Cases ((Bool True, m) NE.:| [])),
         IndexFn Empty cases) -> -- XXX support only 1D arrays for now.
              simplify $ IndexFn (Forall i (Iota m)) cases
        _ -> undefined -- TODO See iota comment.
  | Just "not" <- getFun f,
    [arg] <- getArgs args = do
      IndexFn it body <- forward arg
      rewrite $ IndexFn it (cmapValues (toNNF . Not) body)
forward e = error $ "forward on " <> show e
