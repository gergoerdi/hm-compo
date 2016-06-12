{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards, TupleSections #-}
module Language.HM.Compositional
       ( polyVars, runM
       , tyCheckBinds
       , Typing0(..)
       )
       where

import Language.HM.Monad
import Language.HM.Syntax
import Language.HM.Meta
import Language.HM.Compositional.Error
import Language.HM.Pretty

import Control.Monad.ST
import Control.Unification.Types
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Text.PrettyPrint hiding ((<>))
import qualified Text.PrettyPrint.Boxes as Boxes

import Control.Monad.Except
import Control.Monad.RWS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (sort, nub)

type ErrC s = ErrC0 Ty0 (MVar s)
type Err s loc = Tagged (ErrC s) (loc, Doc)

type MonoCtx s = MonoCtx0 Var Ty0 (MVar s)
type Typing = Typing0 Var Ty0
type MTyping s = Typing (MVar s)

type PolyCtx s = Map Var (MTyping s)
data Ctx s loc = Ctx{ polyVars :: PolyCtx s }

type M s loc = TC (Ctx s loc) (ErrC s) s loc

withMonoVar :: Var -> M s loc a -> M s loc a
withMonoVar v = withMonoVars [v]

withMonoVars :: [Var] -> M s loc a -> M s loc a
withMonoVars vs body = do
    vtys <- traverse monoVar vs
    withPolyVars (Map.fromList vtys) body
  where
    monoVar v = do
        t <- UVar <$> freshVar
        return (v, Map.singleton v t :- t)

withPolyVars :: Map Var (MTyping s) -> M s loc a -> M s loc a
withPolyVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

unzipTypings :: [Typing0 var t v] -> ([MonoCtx0 var t v], [UTerm t v])
unzipTypings typs = unzip [(mc, t) | mc :- t <- typs]

unifyTypings :: [(Doc, MTyping s)] -> [(MTy s, MTy s)] -> M s loc (MonoCtx s)
unifyTypings ucs tyeqs = do
    forM_ tyeqs $ \(t, u) -> runUnify (mkError Nothing) t u
    runUnifies (mkError . Just) mcs
  where
    mcs = [mc | (_ , mc :- _) <- ucs]

    mkError var t u uerr = do
        ucs <- traverse (traverse zonkTyping) ucs
        return $ UErrC ucs var t u uerr

unifyBindings :: MonoCtx s -> (Doc, MTyping s) -> M s loc (MTyping s)
unifyBindings mcBinds uc = do
    mc <- runUnifies mkError [mcBinds, mc]
    return $ mc :- t
  where
    (doc, mc :- t) = uc

    mkError var t u uerr = do
        mcBinds <- traverse zonk mcBinds
        uc <- traverse zonkTyping uc
        return $ BErrC mcBinds uc var t u uerr

runUnifies :: (Var -> MTy s -> MTy s -> UFailure Ty0 (MVar s) -> M s loc (ErrC s))
           -> [MonoCtx s] -> M s loc (MonoCtx s)
runUnifies mkError mcs = flip Map.traverseWithKey (zipMaps mcs) $ \var ts ->
  case ts of
      [] -> UVar <$> freshVar
      [t] -> return t
      (t:us) -> do
          forM_ ts $ \u -> runUnify (mkError var) t u
          return t

runUnify :: (MTy s -> MTy s -> UFailure Ty0 (MVar s) -> M s loc (ErrC s))
         -> MTy s -> MTy s -> M s loc ()
runUnify mkError t u = do
    res <- runExceptT $ unify t u
    case res of
        Left err -> do
            t <- zonk t
            u <- zonk u
            throwError =<< mkError t u err
        Right ok -> return ok

unifyMany :: [MTy s] -> ExceptT (UFailure Ty0 (MVar s)) (M s loc) (MTy s)
unifyMany [] = UVar <$> lift freshVar
unifyMany [t] = return t
unifyMany (t:ts) = do
    mapM_ (unify t) ts
    return t

zonkTyping :: MTyping s -> M s loc (MTyping s)
zonkTyping (mc :- t) = do
    mc <- traverse zonk mc
    t <- zonk t
    return $ mc :- t

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps = Map.unionsWith (++) . map (fmap (:[]))

uctx :: (Pretty a) => a -> MTyping s -> (Doc, MTyping s)
uctx e typ = (pPrint e, typ)

tyInfer :: Term loc -> M s loc (MTyping s)
tyInfer le@(Tagged _ e) = withLoc le $ case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        case vt of
            Just typ -> freshen =<< zonkTyping typ
            Nothing -> throwError $ ErrC $ unwords ["Not in scope:", show v]
    Con dcon -> do
        ct <- askDataCon dcon
        ct <- case ct of
            Nothing -> throwError $ ErrC $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        return $ mempty :- ct
    Lam v e -> do
        mc :- t <- withMonoVar v $ tyInfer e
        u <- maybe (UVar <$> freshVar) return $ Map.lookup v mc
        return $ Map.delete v mc :- (u ~> t)
    App f e -> do
        typ1@(_ :- t) <- tyInfer f
        typ2@(_ :- u) <- tyInfer e
        a <- UVar <$> freshVar
        mc <- unifyTypings [uctx f typ1, uctx e typ2] [(u ~> a, t)]
        return $ mc :- a
    Case e as -> do
        typ0@(mc0 :- t0) <- tyInfer e
        ucs <- forM as $ \(pat, e) -> do
            typPat@(mcPat :- tPat) <- tyInferPat pat
            typ@(mc :- t) <- withMonoVars (Map.keys mcPat) $ tyInfer e
            unifyTypings [uctx e typ, uctx pat typPat] [(t0, tPat)]
            let mc' = mc `Map.difference` mcPat
            return (pPrintAlt pat e, mc' :- t)
        let (_, ts) = unzipTypings (map snd ucs)
        t <- UVar <$> freshVar
        mc <- unifyTypings (uctx e typ0:ucs) $ map (t,) ts
        return $ mc :- t
    Let binds e -> tyCheckBinds binds $ \mcBinds -> do
        typBody <- tyInfer e
        unifyBindings mcBinds (uctx e typBody)

tyInferPat :: Pat loc -> M s loc (MTyping s)
tyInferPat lpat@(Tagged _ pat) = withLoc lpat $ case pat of
    PWild -> do
        t <- UVar <$> freshVar
        return $ mempty :- t
    PVar v -> do
        t <- UVar <$> freshVar
        return $ Map.singleton v t :- t
    PCon dcon ps -> do
        ct <- askDataCon dcon
        ct <- case ct of
            Nothing -> throwError $ ErrC $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t) = tFunArgs ct
        unless (length ps == length tArgs) $
          throwError $ ErrC $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        typs <- traverse tyInferPat ps
        let ucs = zipWith uctx ps typs
            (_, ts) = unzipTypings typs
        mc <- unifyTypings ucs (zip tArgs ts)
        return $ mc :- t

tyCheckBinds :: [(Var, Term loc)] -> (MonoCtx s -> M s loc a) -> M s loc a
tyCheckBinds binds body = go mempty $ partitionBinds binds
  where
    go mc0 (bs:bss) = do
        let newVars = map fst bs
        pc <- withMonoVars newVars $ do
            typings <- traverse (traverse tyInfer) bs
            let typRecs = [Map.singleton v t :- t | (v, _ :- t) <- typings]
                ucs = map (uncurry uctx) typings
                ucRecs = zipWith uctx newVars typRecs
            unifyTypings (ucs ++ ucRecs) []
            let newVarSet = Map.fromList [(v, ()) | v <- newVars]
                unshadow (mc :- t) = (mc `Map.difference` newVarSet) :- t
            return $ fmap unshadow $ Map.fromList typings
        let (mcs, _) = unzipTypings $ Map.elems pc
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: (Pretty loc) => Map DCon PolyTy -> M s loc a -> ST s (Either Doc a)
runM dataCons = runTC dataCons Ctx{..}
  where
    polyVars = mempty
