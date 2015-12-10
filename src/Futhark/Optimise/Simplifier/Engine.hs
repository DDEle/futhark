{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, FlexibleContexts, ScopedTypeVariables #-}
-- |
--
-- Perform general rule-based simplification based on data dependency
-- information.  This module will:
--
--    * Perform common-subexpression elimination (CSE).
--
--    * Hoist expressions out of loops (including lambdas) and
--    branches.  This is done as aggressively as possible.
--
--    * Apply simplification rules (see
--    "Futhark.Optimise.Simplification.Rules").
--
-- If you just want to run the simplifier as simply as possible, you
-- may prefer to use the "Futhark.Optimise.Simplifier" module.
--
module Futhark.Optimise.Simplifier.Engine
       ( -- * Monadic interface
         MonadEngine(..)
       , addBindingEngine
       , collectBindingsEngine
       , Env
       , emptyEnv
       , HoistBlockers(..)
       , noExtraHoistBlockers
       , State
       , emptyState
       , Need
       , asksEngineEnv
       , getVtable
       , localVtable
       , insertAllBindings
       , defaultSimplifyBody
       , defaultInspectBinding
         -- * Building blocks
       , SimplifiableOp (..)
       , Simplifiable (..)
       , simplifyBinding
       , simplifyResult
       , simplifyExp
       , simplifyFun
       , simplifyLambda
       , simplifyLambdaNoHoisting
       , simplifyExtLambda

       , BlockPred
       ) where

import Control.Applicative
import Control.Monad.Writer

import Data.Either
import Data.Hashable
import Data.List
import qualified Data.Traversable
import Data.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Foldable (traverse_)

import Prelude

import qualified Futhark.Representation.AST.Annotations as Annotations
import Futhark.Representation.AST
import Futhark.Optimise.Simplifier.Rule
import qualified Futhark.Analysis.SymbolTable as ST
import qualified Futhark.Analysis.UsageTable as UT
import Futhark.Analysis.Usage
import Futhark.Optimise.Simplifier.Apply
import Futhark.Construct
import qualified Futhark.Analysis.ScalExp as SExp
import Futhark.Optimise.Simplifier.Lore

type NeedSet lore = [Binding lore]

data Need lore = Need { needBindings :: NeedSet lore
                      , usageTable  :: UT.UsageTable
                      }

instance Monoid (Need lore) where
  Need b1 f1 `mappend` Need b2 f2 = Need (b1 <> b2) (f1 <> f2)
  mempty = Need [] UT.empty

type AliasMap = HM.HashMap VName Names

data HoistBlockers m = HoistBlockers
                       { blockHoistPar :: BlockPred (Lore m)
                         -- ^ Blocker for hoisting out of parallel loops.
                       , blockHoistSeq :: BlockPred (Lore m)
                         -- ^ Blocker for hoisting out of sequential loops.
                       }

noExtraHoistBlockers :: HoistBlockers m
noExtraHoistBlockers = HoistBlockers neverBlocks neverBlocks

data Env m = Env { envProgram       :: Maybe (Prog (InnerLore m))
                 , envRules         :: RuleBook m
                 , envAliases       :: AliasMap
                 , envHoistBlockers :: HoistBlockers m
                 }

emptyEnv :: MonadEngine m =>
            RuleBook m
         -> HoistBlockers m
         -> Maybe (Prog (InnerLore m))
         -> Env m
emptyEnv rules blockers prog =
  Env { envProgram = prog
      , envRules = rules
      , envAliases = mempty
      , envHoistBlockers = blockers
      }
data State m = State { stateVtable :: ST.SymbolTable (Lore m)
                     }

emptyState :: State m
emptyState = State { stateVtable = ST.empty }

class (MonadBinder m,
       Proper (Lore m),
       Proper (InnerLore m),
       Lore m ~ Wise (InnerLore m),
       Simplifiable (Annotations.LetBound (InnerLore m)),
       Simplifiable (Annotations.FParam (InnerLore m)),
       Simplifiable (Annotations.LParam (InnerLore m)),
       Simplifiable (Annotations.RetType (InnerLore m)),
       SimplifiableOp (InnerLore m) (Op (InnerLore m))) => MonadEngine m where
  type InnerLore m :: *
  askEngineEnv :: m (Env m)
  localEngineEnv :: (Env m -> Env m) -> m a -> m a
  tellNeed :: Need (Lore m) -> m ()
  listenNeed :: m a -> m (a, Need (Lore m))
  getEngineState :: m (State m)
  putEngineState :: State m -> m ()
  passNeed :: m (a, Need (Lore m) -> Need (Lore m)) -> m a

  simplifyBody :: [Diet] -> Body (InnerLore m) -> m Result
  simplifyBody = defaultSimplifyBody
  inspectBinding :: Binding (Lore m) -> m ()
  inspectBinding = defaultInspectBinding

addBindingEngine :: MonadEngine m =>
                    Binding (Lore m) -> m ()
addBindingEngine bnd = do
  modifyVtable $ ST.insertBinding bnd
  case bindingExp bnd of
    PrimOp (Assert se _) -> asserted se
    _                    -> return ()
  needBinding bnd

collectBindingsEngine :: MonadEngine m =>
                         m a -> m (a, [Binding (Lore m)])
collectBindingsEngine m = passNeed $ do
  (x, need) <- listenNeed m
  return ((x, needBindings need),
          const mempty)

asksEngineEnv :: MonadEngine m => (Env m -> a) -> m a
asksEngineEnv f = f <$> askEngineEnv

getsEngineState :: MonadEngine m => (State m -> a) -> m a
getsEngineState f = f <$> getEngineState

modifyEngineState :: MonadEngine m => (State m -> State m) -> m ()
modifyEngineState f = do x <- getEngineState
                         putEngineState $ f x

needBinding :: MonadEngine m => Binding (Lore m) -> m ()
needBinding bnd = tellNeed $ Need [bnd] UT.empty

boundFree :: MonadEngine m => Names -> m ()
boundFree fs = tellNeed $ Need [] $ UT.usages fs

usedName :: MonadEngine m => VName -> m ()
usedName = boundFree . HS.singleton

consumedName :: MonadEngine m => VName -> m ()
consumedName = tellNeed . Need [] . UT.consumedUsage

inResultName :: MonadEngine m => VName -> m ()
inResultName = tellNeed . Need [] . UT.inResultUsage

asserted :: MonadEngine m => SubExp -> m ()
asserted Constant{} =
  return ()
asserted (Var name) = do
  se <- ST.lookupExp name <$> getVtable
  case se of Just (PrimOp (BinOp Equal x y _)) -> do
               case x of Var xvar ->
                           tellNeed $ Need [] $
                           UT.equalToUsage xvar y
                         _ -> return ()
               case y of Var yvar ->
                           tellNeed $ Need [] $
                           UT.equalToUsage yvar x
                         _ -> return ()
             _ -> return ()

tapUsage :: MonadEngine m => m a -> m (a, UT.UsageTable)
tapUsage m = do (x,needs) <- listenNeed m
                return (x, usageTable needs)

blockUsage :: MonadEngine m => m a -> m a
blockUsage m = passNeed $ do
  (x, _) <- listenNeed m
  return (x, const mempty)

censorUsage :: MonadEngine m =>
               (UT.UsageTable -> UT.UsageTable)
            -> m a -> m a
censorUsage f m = passNeed $ do
  x <- m
  return (x, \acc -> acc { usageTable = f $ usageTable acc })

getVtable :: MonadEngine m => m (ST.SymbolTable (Lore m))
getVtable = getsEngineState stateVtable

putVtable :: MonadEngine m => ST.SymbolTable (Lore m) -> m ()
putVtable vtable = modifyEngineState $ \s -> s { stateVtable = vtable }

modifyVtable :: MonadEngine m => (ST.SymbolTable (Lore m) -> ST.SymbolTable (Lore m))
             -> m ()
modifyVtable f = do vtable <- getVtable
                    putVtable $ f vtable

localVtable :: MonadEngine m =>
               (ST.SymbolTable (Lore m) -> ST.SymbolTable (Lore m))
            -> m a -> m a
localVtable f m = do
  vtable <- getVtable
  modifyEngineState $ \env -> env { stateVtable = f vtable }
  (x, need) <- listenNeed m
  let vtable' = foldl (flip ST.insertBinding) vtable $ needBindings need
  modifyEngineState $ \env -> env { stateVtable = vtable' }
  return x

enterLoop :: MonadEngine m => m a -> m a
enterLoop = localVtable ST.deepen

enterBody :: MonadEngine m => m a -> m a
enterBody = censorUsage UT.leftScope

bindFParams :: MonadEngine m =>
               [FParam (Lore m)] -> m a -> m a
bindFParams params =
  localVtable $ ST.insertFParams params

bindLParams :: MonadEngine m =>
               [LParam (Lore m)] -> m a -> m a
bindLParams params =
  localVtable $ \vtable ->
    foldr ST.insertLParam vtable params

bindArrayLParams :: MonadEngine m =>
                    [(LParam (Lore m),Maybe VName)] -> m a -> m a
bindArrayLParams params =
  localVtable $ \vtable ->
    foldr (uncurry ST.insertArrayLParam) vtable params

bindLoopVar :: MonadEngine m => VName -> SubExp -> m a -> m a
bindLoopVar var bound =
  localVtable $ clampUpper . clampVar
  where clampVar = ST.insertLoopVar var bound
        -- If we enter the loop, then 'bound' is at least one.
        clampUpper = case bound of Var v -> ST.isAtLeast v 1
                                   _     -> id

bindLoopVars :: MonadEngine m => [(VName,SubExp)] -> m a -> m a
bindLoopVars []                  m =
  m
bindLoopVars ((var,bound):lvars) m =
  bindLoopVar var bound $ bindLoopVars lvars m

hoistBindings :: MonadEngine m =>
                 RuleBook m -> BlockPred (Lore m)
              -> ST.SymbolTable (Lore m) -> UT.UsageTable
              -> [Binding (Lore m)] -> Result
              -> m (Body (Lore m),
                    [Binding (Lore m)],
                    UT.UsageTable)
hoistBindings rules block vtable uses needs result = do
  (uses', blocked, hoisted) <- simplifyBindings vtable uses needs
  mapM_ addBinding blocked
  body <- mkBodyM blocked result
  return (body, hoisted, uses')
  where simplifyBindings vtable' uses' bnds = do
          (uses'', bnds') <- simplifyBindings' vtable' uses' bnds
          -- We need to do a final pass to ensure that nothing is
          -- hoisted past something that it depends on.
          let (blocked, hoisted) = partitionEithers $ blockUnhoistedDeps bnds'
          return (uses'', blocked, hoisted)

        simplifyBindings' vtable' uses' bnds =
          foldM hoistable (uses',[]) $ reverse $ zip bnds vtables
            where vtables = scanl (flip ST.insertBinding) vtable' bnds

        hoistable (uses',bnds) (bnd, vtable')
          | not $ uses' `UT.contains` provides bnd = -- Dead binding.
            return (uses', bnds)
          | otherwise = do
            res <- localVtable (const vtable') $
                   bottomUpSimplifyBinding rules (vtable', uses') bnd
            case res of
              Nothing -- Nothing to optimise - see if hoistable.
                | block uses' bnd ->
                  return (expandUsage uses' bnd `UT.without` provides bnd,
                          Left bnd : bnds)
                | otherwise ->
                  return (expandUsage uses' bnd, Right bnd : bnds)
              Just optimbnds -> do
                (uses'',bnds') <- simplifyBindings' vtable' uses' optimbnds
                return (uses'', bnds'++bnds)

blockUnhoistedDeps :: Proper lore =>
                      [Either (Binding lore) (Binding lore)]
                   -> [Either (Binding lore) (Binding lore)]
blockUnhoistedDeps = snd . mapAccumL block HS.empty
  where block blocked (Left need) =
          (blocked <> HS.fromList (provides need), Left need)
        block blocked (Right need)
          | blocked `intersects` requires need =
            (blocked <> HS.fromList (provides need), Left need)
          | otherwise =
            (blocked, Right need)

provides :: Proper lore => Binding lore -> [VName]
provides = patternNames . bindingPattern

requires :: Proper lore => Binding lore -> Names
requires bnd =
  (mconcat (map freeIn $ patternElements $ bindingPattern bnd)
  `HS.difference` HS.fromList (provides bnd)) <>
  freeInExp (bindingExp bnd)

expandUsage :: (Proper lore, Aliased lore) =>
               UT.UsageTable -> Binding lore -> UT.UsageTable
expandUsage utable bnd = utable <> usageInBinding bnd <> usageThroughAliases
  where pat = bindingPattern bnd
        usageThroughAliases =
          mconcat $ mapMaybe usageThroughBindeeAliases $
          zip (patternNames pat) (patternAliases pat)
        usageThroughBindeeAliases (name, aliases) = do
          uses <- UT.lookup name utable
          return $ mconcat $ map (`UT.usage` uses) $ HS.toList aliases

intersects :: (Eq a, Hashable a) => HS.HashSet a -> HS.HashSet a -> Bool
intersects a b = not $ HS.null $ a `HS.intersection` b

type BlockPred lore = UT.UsageTable -> Binding lore -> Bool

neverBlocks :: BlockPred lore
neverBlocks _ _ = False

isFalse :: Bool -> BlockPred lore
isFalse b _ _ = not b

orIf :: BlockPred lore -> BlockPred lore -> BlockPred lore
orIf p1 p2 body need = p1 body need || p2 body need

isConsumed :: BlockPred lore
isConsumed utable = any (`UT.isConsumed` utable) . patternNames . bindingPattern

blockIf :: MonadEngine m =>
           BlockPred (Lore m)
        -> m Result -> m (Body (Lore m))
blockIf block m = passNeed $ do
  (body, needs) <- listenNeed m
  vtable <- getVtable
  rules <- asksEngineEnv envRules
  (e, hoistable, usages) <-
    hoistBindings rules block vtable (usageTable needs) (needBindings needs) body
  putVtable $ foldl (flip ST.insertBinding) vtable hoistable
  return (e,
          const Need { needBindings = hoistable
                     , usageTable  = usages
                     })

insertAllBindings :: MonadEngine m => m Result -> m (Body (Lore m))
insertAllBindings = blockIf $ \_ _ -> True

hasFree :: Proper lore => Names -> BlockPred lore
hasFree ks _ need = ks `intersects` requires need

isNotSafe :: Proper lore => BlockPred lore
isNotSafe _ = not . safeExp . bindingExp

isInPlaceBound :: BlockPred m
isInPlaceBound _ = not . all ((==BindVar) . patElemBindage) .
                   patternElements . bindingPattern

isNotCheap :: BlockPred m
isNotCheap _ = not . cheapBnd
  where cheapBnd = cheap . bindingExp
        cheap (PrimOp BinOp{})   = True
        cheap (PrimOp SubExp{})  = True
        cheap (PrimOp Not{})     = True
        cheap (PrimOp Negate{})  = True
        cheap LoopOp{}           = False
        cheap _                  = True -- Used to be False, but
                                        -- let's try it out.
hoistCommon :: MonadEngine m =>
               m Result
            -> (ST.SymbolTable (Lore m)
                -> ST.SymbolTable (Lore m))
            -> m Result
            -> (ST.SymbolTable (Lore m)
                -> ST.SymbolTable (Lore m))
            -> m (Body (Lore m), Body (Lore m))
hoistCommon m1 vtablef1 m2 vtablef2 = passNeed $ do
  (body1, needs1) <- listenNeed $ localVtable vtablef1 m1
  (body2, needs2) <- listenNeed $ localVtable vtablef2 m2
  let block = isNotSafe `orIf` isNotCheap `orIf` isInPlaceBound
  vtable <- getVtable
  rules <- asksEngineEnv envRules
  (body1', safe1, f1) <-
    enterBody $
    localVtable vtablef1 $
    hoistBindings rules block vtable (usageTable needs1)
    (needBindings needs1) body1
  (body2', safe2, f2) <-
    enterBody $
    localVtable vtablef2 $
    hoistBindings rules block vtable (usageTable needs2)
    (needBindings needs2) body2
  let hoistable = safe1 <> safe2
  putVtable $ foldl (flip ST.insertBinding) vtable hoistable
  return ((body1', body2'),
          const Need { needBindings = hoistable
                     , usageTable = f1 <> f2
                     })

-- | Simplify a single 'Body' inside an arbitrary 'MonadEngine'.
defaultSimplifyBody :: MonadEngine m =>
                       [Diet] -> Body (InnerLore m) -> m Result

defaultSimplifyBody ds (Body _ bnds res) = do
  mapM_ simplifyBinding bnds
  simplifyResult ds res

-- | Simplify a single 'Result' inside an arbitrary 'MonadEngine'.
simplifyResult :: MonadEngine m =>
                  [Diet] -> Result -> m Result

simplifyResult ds es = do
  es' <- mapM simplify es
  consumeResult $ zip ds es'
  return es'

isDoLoopResult :: MonadEngine m =>
                  Result -> m ()
isDoLoopResult = mapM_ checkForVar
  where checkForVar (Var ident) =
          inResultName ident
        checkForVar _ =
          return ()

-- | Simplify the binding, adding it to the program being constructed.
simplifyBinding :: MonadEngine m =>
                   Binding (InnerLore m)
                -> m ()
-- The simplification rules cannot handle Apply, because it requires
-- access to the full program.  This is a bit of a hack.
simplifyBinding (Let pat _ (Apply fname args rettype)) = do
  args' <- mapM (simplify . fst) args
  rettype' <- simplify rettype
  prog <- asksEngineEnv envProgram
  vtable <- getVtable
  case join $ pure simplifyApply <*> prog <*> pure vtable <*> pure fname <*> pure args of
    -- Array values are non-unique, so we may need to copy them.
    Just vs -> do let vs' = valueShapeContext (retTypeValues rettype) vs ++ vs
                  bnds <- forM (zip (patternIdents pat) vs') $ \(p,v) ->
                    case uniqueness $ toDecl (identType p) Unique of
                      Unique    -> mkLetNamesM' [identName p] =<< eCopy (eValue v)
                      Nonunique -> mkLetNamesM' [identName p] =<< eValue v
                  mapM_ (simplifyBinding . removeBindingWisdom) bnds
    Nothing -> do let e' = Apply fname (zip args' $ map snd args) rettype'
                  pat' <- blockUsage $ simplifyPattern pat
                  inspectBinding =<<
                    mkLetM (addWisdomToPattern pat' e') e'

simplifyBinding (Let pat _ lss@(LoopOp Stream{})) = do
  lss' <- simplifyExp lss
  rtp <- expExtType lss
  rtp' <- expExtType lss'
  let patels      = patternElements pat
      argpattps   = map patElemType $ drop (length patels - length rtp) patels
  (newpats,newsubexps) <- unzip <$> reverse <$>
                          foldM gatherPat [] (zip3 rtp rtp' argpattps)
  newexps' <- forM newsubexps $ simplifyExp . PrimOp . SubExp
  newpats' <- mapM simplifyPattern newpats
  let rmvdpatels = concatMap patternElements newpats
      patels' = concatMap (\p->if p `elem` rmvdpatels then [] else [p]) patels
  pat' <- let (ctx,vals) = splitAt (length patels' - length rtp') patels'
          in simplifyPattern $ Pattern ctx vals
  let newpatexps' = zip newpats' newexps' ++ [(pat',lss')]
  newpats'' <- mapM simplifyPattern $ newpats' ++ [pat']
  let (_,newexps'') = unzip newpatexps'
  let newpatexps''= zip newpats'' newexps''
  _ <- forM newpatexps'' $ \(p,e) -> inspectBinding =<<
                            mkLetM (addWisdomToPattern p e) e
  return ()
    where gatherPat acc (_, Basic _, _) = return acc
          gatherPat acc (_, Mem {}, _) = return acc
          gatherPat acc (Array _ shp _, Array _ shp' _, Array _ pshp _) =
            foldM gatherShape acc (zip3 (extShapeDims shp) (extShapeDims shp') (shapeDims pshp))
          gatherPat _ _ =
            fail $ "In simplifyBinding \"let pat = stream()\": "++
                   " reached unreachable case!"
          gatherShape acc (Ext i, Free se', Var pid) = do
            let patind  = elemIndex pid $
                          map patElemName $ patternElements pat
            case patind of
              Just k -> return $ (Pattern [] [patternElements pat !! k], se') : acc
              Nothing-> fail $ "In simplifyBinding \"let pat = stream()\": pat "++
                               "element of known dim not found: "++pretty pid++" "++show i++" "++pretty se'++"."
          gatherShape _ (Free se, Ext i', _) =
            fail $ "In simplifyBinding \"let pat = stream()\": "++
                   " previous known dimension: " ++ pretty se ++
                   " becomes existential: ?" ++ show i' ++ "!"
          gatherShape acc _ = return acc

simplifyBinding (Let pat _ e) = do
  e' <- simplifyExp e
  pat' <- simplifyPattern pat
  inspectBinding =<<
    mkLetM (addWisdomToPattern pat' e') e'

defaultInspectBinding :: MonadEngine m =>
                         Binding (Lore m) -> m ()

defaultInspectBinding bnd = do
  vtable <- getVtable
  rules <- asksEngineEnv envRules
  simplified <- topDownSimplifyBinding rules vtable bnd
  case simplified of
    Just newbnds -> mapM_ inspectBinding newbnds
    Nothing      -> addBinding bnd

simplifyExp :: MonadEngine m => Exp (InnerLore m) -> m (Exp (Lore m))

simplifyExp (If cond tbranch fbranch ts) = do
  -- Here, we have to check whether 'cond' puts a bound on some free
  -- variable, and if so, chomp it.  We should also try to do CSE
  -- across branches.
  cond' <- simplify cond
  ts' <- mapM simplify ts
  let ds = map (const Observe) ts'
  (tbranch',fbranch') <-
    hoistCommon (simplifyBody ds tbranch) (ST.updateBounds True cond)
                (simplifyBody ds fbranch) (ST.updateBounds False cond)
  return $ If cond' tbranch' fbranch' ts'

simplifyExp (LoopOp op) = LoopOp <$> simplifyLoopOp op

simplifyExp (SegOp op) = SegOp <$> simplifySegOp op

simplifyExp e = simplifyExpBase e

simplifyExpBase :: MonadEngine m => Exp (InnerLore m) -> m (Exp (Lore m))
simplifyExpBase = mapExpM hoist
  where hoist = Mapper {
                -- Bodies are handled explicitly because we need to
                -- provide their result diet.
                  mapOnBody = fail "Unhandled body in simplification engine."
                , mapOnSubExp = simplify
                -- Lambdas are handled explicitly because we need to
                -- bind their parameters.
                , mapOnLambda = fail "Unhandled lambda in simplification engine."
                , mapOnExtLambda = fail "Unhandled existential lambda in simplification engine."
                , mapOnVName = simplify
                , mapOnCertificates = simplify
                , mapOnRetType = simplify
                , mapOnFParam =
                  fail "Unhandled FParam in simplification engine."
                , mapOnLParam =
                  fail "Unhandled LParam in simplification engine."
                , mapOnOp =
                  simplifyOp
                }

simplifyLoopOp :: MonadEngine m => LoopOp (InnerLore m) -> m (LoopOp (Lore m))

simplifyLoopOp (DoLoop respat merge form loopbody) = do
  let (mergepat, mergeexp) = unzip merge
  mergepat' <- mapM (simplifyParam simplify) mergepat
  mergeexp' <- mapM simplify mergeexp
  let diets = map (diet . paramDeclType) mergepat'
  (form', boundnames, wrapbody) <- case form of
    ForLoop loopvar boundexp -> do
      boundexp' <- simplify boundexp
      return (ForLoop loopvar boundexp',
              loopvar `HS.insert` fparamnames,
              bindLoopVar loopvar boundexp')
    WhileLoop cond -> do
      cond' <- simplify cond
      return (WhileLoop cond',
              fparamnames,
              id)
  seq_blocker <- asksEngineEnv $ blockHoistSeq . envHoistBlockers
  loopbody' <- enterLoop $ enterBody $
               bindFParams mergepat' $
               blockIf
               (hasFree boundnames `orIf` isConsumed `orIf` seq_blocker) $
               wrapbody $ do
                 res <- simplifyBody diets loopbody
                 isDoLoopResult res
                 return res
  let merge' = zip mergepat' mergeexp'
  consumeResult $ zip diets mergeexp'
  return $ DoLoop respat merge' form' loopbody'
  where fparamnames = HS.fromList (map (paramName . fst) merge)

simplifyLoopOp (Stream cs outerdim form lam arr ii) = do
  cs' <- simplify      cs
  outerdim' <- simplify outerdim
  form' <- simplifyStreamForm outerdim' form
  arr' <- mapM simplify  arr
  vtab <- getVtable
  let (chunk:_) = extLambdaParams lam
      se_outer = case outerdim' of
                    Var idd    -> fromMaybe (SExp.Id idd Int) (ST.lookupScalExp idd vtab)
                    Constant c -> SExp.Val c
      se_1 = SExp.Val $ IntVal 1
      -- extension: one may similarly treat iota stream-array case,
      -- by setting the bounds to [0, se_outer-1]
      parbnds  = [ (chunk, se_1, se_outer) ]
  lam' <- simplifyExtLambda parbnds lam outerdim'
  return $ Stream cs' outerdim' form' lam' arr' ii
  where simplifyStreamForm _ (MapLike o) = return $ MapLike o
        simplifyStreamForm outerdim' (RedLike o lam0 acc) = do
            acc'  <- mapM simplify acc
            lam0' <- simplifyLambda lam0 outerdim' $
                     replicate (length $ lambdaParams lam0) Nothing
            return $ RedLike o lam0' acc'
        simplifyStreamForm _ (Sequential acc) = do
            acc'  <- mapM simplify acc
            return $ Sequential acc'

simplifyLoopOp (MapKernel cs w index ispace inps returns body) = do
  cs' <- simplify cs
  w' <- simplify w
  ispace' <- forM ispace $ \(i, bound) -> do
    bound' <- simplify bound
    return (i, bound')
  returns' <- forM returns $ \(t, perm) -> do
    t' <- simplify t
    return (t', perm)
  par_blocker <- asksEngineEnv $ blockHoistPar . envHoistBlockers
  enterLoop $ enterBody $ bindLoopVars ((index,w) : ispace) $ do
    inps' <- mapM simplifyKernelInput inps
    body' <- bindLParams (map kernelInputParam inps') $
             blockIf (hasFree bound_here `orIf` isConsumed `orIf` par_blocker) $
             simplifyBody (map (const Observe) returns) body
    return $ MapKernel cs' w' index ispace' inps' returns' body'
  where bound_here = HS.fromList $ map kernelInputName inps ++ map fst ispace

simplifyLoopOp (ReduceKernel cs w kernel_size parlam seqlam nes arrs) = do
  cs' <- simplify cs
  w' <- simplify w
  kernel_size' <- simplify kernel_size
  nes' <- mapM simplify nes
  arrs' <- mapM simplify arrs
  parlam' <- simplifyLambda parlam w' $ map (const Nothing) nes
  seqlam' <- simplifyLambda seqlam w' $ map (const Nothing) nes
  return $ ReduceKernel cs' w' kernel_size' parlam' seqlam' nes' arrs'

simplifyLoopOp (ScanKernel cs w kernel_size order lam input) = do
  let (nes, arrs) = unzip input
  cs' <- simplify cs
  w' <- simplify w
  kernel_size' <- simplify kernel_size
  nes' <- mapM simplify nes
  arrs' <- mapM simplify arrs
  lam' <- simplifyLambda lam w' $ map Just arrs'
  return $ ScanKernel cs' w' kernel_size' order lam' $ zip nes' arrs'

simplifyLoopOp (Map cs w fun arrs) = do
  cs' <- simplify cs
  w' <- simplify w
  arrs' <- mapM simplify arrs
  fun' <- simplifyLambda fun w $ map Just arrs'
  return $ Map cs' w' fun' arrs'

simplifyLoopOp (ConcatMap cs w fun arrs) = do
  cs' <- simplify cs
  w' <- simplify w
  arrs' <- mapM (mapM simplify) arrs
  fun' <- simplifyLambda fun w $ map (const Nothing) $ lambdaParams fun
  return $ ConcatMap cs' w' fun' arrs'

simplifyLoopOp (Reduce cs w fun input) = do
  let (acc, arrs) = unzip input
  cs' <- simplify cs
  w' <- simplify w
  acc' <- mapM simplify acc
  arrs' <- mapM simplify arrs
  fun' <- simplifyLambda fun w $ map Just arrs'
  return $ Reduce cs' w' fun' (zip acc' arrs')

simplifyLoopOp (Scan cs w fun input) = do
  let (acc, arrs) = unzip input
  cs' <- simplify cs
  w' <- simplify w
  acc' <- mapM simplify acc
  arrs' <- mapM simplify arrs
  fun' <- simplifyLambda fun w $ map Just arrs'
  return $ Scan cs' w' fun' (zip acc' arrs')

simplifyLoopOp (Redomap cs w outerfun innerfun acc arrs) = do
  cs' <- simplify cs
  w' <- simplify w
  acc' <- mapM simplify acc
  arrs' <- mapM simplify arrs
  outerfun' <- simplifyLambda outerfun w $
               replicate (length $ lambdaParams outerfun) Nothing
  (innerfun', used) <- tapUsage $ simplifyLambda innerfun w $ map Just arrs
  (innerfun'', arrs'') <- removeUnusedParams used innerfun' arrs'
  return $ Redomap cs' w' outerfun' innerfun'' acc' arrs''
  where removeUnusedParams used lam arrinps
          | (accparams, arrparams) <- splitAt (length acc) $ lambdaParams lam =
              let (arrparams', arrinps') =
                    unzip $ filter ((`UT.used` used) . paramName . fst) $
                    zip arrparams arrinps
              in return (lam { lambdaParams = accparams ++ arrparams' },
                         arrinps')
          | otherwise = return (lam, arrinps)

simplifySegOp :: MonadEngine m => SegOp (InnerLore m) -> m (SegOp (Lore m))
simplifySegOp (SegReduce cs w fun input descp) = do
  let (acc, arrs) = unzip input
  cs' <- simplify cs
  w' <- simplify w
  acc' <- mapM simplify acc
  arrs' <- mapM simplify arrs
  fun' <- simplifyLambda fun w $ map Just arrs'
  descp' <- simplify descp
  return $ SegReduce cs' w' fun' (zip acc' arrs') descp'

simplifySegOp (SegScan cs w st fun input descp) = do
  let (acc, arrs) = unzip input
  cs' <- simplify cs
  w' <- simplify w
  acc' <- mapM simplify acc
  arrs' <- mapM simplify arrs
  fun' <- simplifyLambda fun w $ map Just arrs'
  descp' <- simplify descp
  return $ SegScan cs' w' st fun' (zip acc' arrs') descp'

simplifySegOp (SegReplicate cs counts dataarr seg) = do
  cs' <- simplify cs
  counts' <- simplify counts
  dataarr' <- simplify dataarr
  seg' <- Data.Traversable.mapM simplify seg
  return $ SegReplicate cs' counts' dataarr' seg'

class CanBeWise op => SimplifiableOp lore op where
  simplifyOp :: (MonadEngine m, InnerLore m ~ lore) => op -> m (OpWithWisdom op)

instance SimplifiableOp lore () where
  simplifyOp () = return ()

class Simplifiable e where
  simplify :: MonadEngine m => e -> m e

instance (Simplifiable a, Simplifiable b) => Simplifiable (a, b) where
  simplify (x,y) = do
    x' <- simplify x
    y' <- simplify y
    return (x', y')

instance Simplifiable a => Simplifiable (Maybe a) where
  simplify Nothing = return Nothing
  simplify (Just x) = Just <$> simplify x

instance Simplifiable SubExp where
  simplify (Var name) = do
    bnd <- getsEngineState $ ST.lookupSubExp name . stateVtable
    case bnd of
      Just (Constant v) -> return $ Constant v
      Just (Var id') -> do usedName id'
                           return $ Var id'
      _              -> do usedName name
                           return $ Var name
  simplify (Constant v) =
    return $ Constant v

instance Simplifiable KernelSize where
  simplify (KernelSize num_groups group_size thread_chunk
            num_elements offset_multiple num_threads) = do
    num_groups' <- simplify num_groups
    group_size' <- simplify group_size
    thread_chunk' <- simplify thread_chunk
    num_elements' <- simplify num_elements
    offset_multiple' <- simplify offset_multiple
    num_threads' <- simplify num_threads
    return $ KernelSize num_groups' group_size' thread_chunk' num_elements' offset_multiple' num_threads'

instance Simplifiable ExtRetType where
  simplify = liftM ExtRetType . mapM simplify . retTypeValues

simplifyPattern :: MonadEngine m =>
                   Pattern (InnerLore m)
                -> m (Pattern (InnerLore m))
simplifyPattern pat =
  Pattern <$>
  mapM inspect (patternContextElements pat) <*>
  mapM inspect (patternValueElements pat)
  where inspect (PatElem name bindage lore) = do
          bindage' <- simplify bindage
          lore'  <- simplify lore
          return $ PatElem name bindage' lore'

instance Simplifiable Bindage where
  simplify BindVar =
    return BindVar
  simplify (BindInPlace cs src is) =
    BindInPlace <$>
    simplify cs <*>
    simplify src <*>
    mapM simplify is

simplifyParam :: MonadEngine m =>
                 (attr -> m attr) -> ParamT attr -> m (ParamT attr)
simplifyParam simplifyAttribute (Param name attr) = do
  attr' <- simplifyAttribute attr
  return $ Param name attr'

instance Simplifiable VName where
  simplify v = do
    se <- ST.lookupSubExp v <$> getVtable
    case se of
      Just (Var v') -> do usedName v'
                          return v'
      _             -> do usedName v
                          return v

instance Simplifiable (TypeBase ExtShape u) where
  simplify t = do shape <- simplify $ arrayShape t
                  return $ t `setArrayShape` shape

instance Simplifiable ExtShape where
  simplify = liftM ExtShape . mapM simplify . extShapeDims

instance Simplifiable ExtDimSize where
  simplify (Free se) = Free <$> simplify se
  simplify (Ext x)   = return $ Ext x

instance Simplifiable (TypeBase Shape u) where
  simplify (Array et shape u) = do
    dims <- mapM simplify $ shapeDims shape
    return $ Array et (Shape dims) u
  simplify (Mem size space) =
    Mem <$> simplify size <*> pure space
  simplify (Basic bt) =
    return $ Basic bt

simplifyLambda :: MonadEngine m =>
                  Lambda (InnerLore m)
               -> SubExp -> [Maybe VName]
               -> m (Lambda (Lore m))
simplifyLambda = simplifyLambdaMaybeHoist True

simplifyLambdaNoHoisting :: MonadEngine m =>
                            Lambda (InnerLore m)
                         -> SubExp -> [Maybe VName]
                         -> m (Lambda (Lore m))
simplifyLambdaNoHoisting = simplifyLambdaMaybeHoist False

simplifyLambdaMaybeHoist :: MonadEngine m =>
                            Bool -> Lambda (InnerLore m)
                         -> SubExp -> [Maybe VName]
                         -> m (Lambda (Lore m))
simplifyLambdaMaybeHoist hoisting lam@(Lambda i params body rettype) w arrs = do
  params' <- mapM (simplifyParam simplify) params
  let (nonarrayparams, arrayparams) =
        splitAt (length params' - length arrs) params'
      paramnames = HS.fromList $ boundByLambda lam
  par_blocker <- asksEngineEnv $ blockHoistPar . envHoistBlockers
  body' <-
    enterLoop $ enterBody $
    bindLoopVar i w $
    bindLParams nonarrayparams $
    bindArrayLParams (zip arrayparams arrs) $
    blockIf (isFalse hoisting `orIf` hasFree paramnames `orIf` isConsumed `orIf` par_blocker) $
      simplifyBody (map (const Observe) rettype) body
  rettype' <- mapM simplify rettype
  return $ Lambda i params' body' rettype'

simplifyExtLambda :: MonadEngine m =>
                    [(LParam (Lore m), SExp.ScalExp, SExp.ScalExp)]
                  ->    ExtLambda (InnerLore m)
                  -> SubExp
                  -> m (ExtLambda (Lore m))
simplifyExtLambda parbnds lam@(ExtLambda index params body rettype) w = do
  params' <- mapM (simplifyParam simplify) params
  let paramnames = HS.fromList $ boundByExtLambda lam
  rettype' <- mapM simplify rettype
  body' <- enterLoop $ enterBody $
           bindLoopVar index w $
           bindLParams params' $
           blockIf (hasFree paramnames `orIf` isConsumed) $
           localVtable extendSymTab $
           simplifyBody (map (const Observe) rettype) body
  let bodyres = bodyResult body'
      bodyenv = typeEnvFromBindings $ bodyBindings body'
  rettype'' <- bindLParams params' $
               zipWithM (refineArrType bodyenv params') bodyres rettype'
  return $ ExtLambda index params' body' rettype''
    where extendSymTab vtb =
            foldl (\ vt (i,l,u) ->
                        let i_name = paramName i
                        in  ST.setUpperBound i_name u $
                            ST.setLowerBound i_name l vt
                  ) vtb parbnds
          refineArrType :: MonadEngine m =>
                           TypeEnv -> [LParam (Lore m)] -> SubExp -> ExtType -> m ExtType
          refineArrType bodyenv pars x (Array btp shp u) = do
            vtab <- ST.bindings <$> getVtable
            dsx <- flip extendedTypeEnv bodyenv $
                   shapeDims <$> arrayShape <$> subExpType x
            let parnms = map paramName pars
                dsrtpx =  extShapeDims shp
                (resdims,_) =
                    foldl (\ (lst,i) el ->
                            case el of
                              (Free (Constant c), _) -> (lst++[Free (Constant c)], i)
                              ( _,      Constant c ) -> (lst++[Free (Constant c)], i)
                              (Free (Var tid), Var pid) ->
                                if not (HM.member tid vtab) &&
                                        HM.member pid vtab
                                then (lst++[Free (Var pid)], i)
                                else (lst++[Free (Var tid)], i)
                              (Ext _, Var pid) ->
                                if HM.member pid vtab ||
                                   pid `elem` parnms
                                then (lst ++ [Free (Var pid)], i)
                                else (lst ++ [Ext i],        i+1)
                          ) ([],0) (zip dsrtpx dsx)
            return $ Array btp (ExtShape resdims) u
          refineArrType _ _ _ tp = return tp

consumeResult :: MonadEngine m =>
                 [(Diet, SubExp)] -> m ()
consumeResult = mapM_ inspect
  where inspect (Consume, se) =
          traverse_ consumedName $ subExpAliases se
        inspect (Observe, _) = return ()

instance Simplifiable Certificates where
  simplify = liftM (nub . concat) . mapM check
    where check idd = do
            vv <- getsEngineState $ ST.lookupSubExp idd . stateVtable
            case vv of
              Just (Constant Checked) -> return []
              Just (Var idd') -> do usedName idd'
                                    return [idd']
              _ -> do usedName idd
                      return [idd]

simplifyKernelInput :: MonadEngine m =>
                       KernelInput (InnerLore m) -> m (KernelInput (Lore m))
simplifyKernelInput (KernelInput param arr is) = do
  param' <- simplifyParam simplify param
  arr' <- simplify arr
  is' <- mapM simplify is
  return $ KernelInput param' arr' is'

simplifyFun :: MonadEngine m =>
               FunDec (InnerLore m) -> m (FunDec (Lore m))
simplifyFun (FunDec fname rettype params body) = do
  rettype' <- simplify rettype
  body' <- bindFParams params $ insertAllBindings $
           simplifyBody (map diet $ retTypeValues rettype') body
  return $ FunDec fname rettype' params body'
