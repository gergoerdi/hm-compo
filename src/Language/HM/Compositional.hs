{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Language.HM.Compositional where

import Language.HM.Monad
import Language.HM.Syntax
import Language.HM.Meta
import Language.HM.Error
import Text.Parsec.Pos

import Control.Monad.ST
import Control.Unification.Types
import Text.PrettyPrint.HughesPJClass (Doc, Pretty)

import Control.Monad.Except
import Control.Monad.RWS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

type Err s loc = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)

instance UErr (Err0 t v) t v where
    uerr = UErr

data Typing0 var t v = Map var (UTerm t v) :- (UTerm t v)

instance (Functor t) => Functor (Typing0 var t) where
    fmap f (mc :- t) = fmap (fmap f) mc :- fmap f t

instance (Foldable t) => Foldable (Typing0 var t) where
    foldMap f (mc :- t) = foldMap (foldMap f) mc <> foldMap f t

instance (Traversable t) => Traversable (Typing0 var t) where
    traverse f (mc :- t) = (:-) <$> traverse (traverse f) mc <*> traverse f t

type Typing = Typing0 Var Ty0
type MTyping s = Typing (MVar s)

data Ctx s loc = Ctx{ polyVars :: Map Var (MTyping s) }

type M s loc = TC (Ctx s loc) (Err0 Ty0 (MVar s)) s loc

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

unzipTypings :: [Typing0 var t v] -> ([Map var (UTerm t v)], [UTerm t v])
unzipTypings typs = unzip [(mc, t) | mc :- t <- typs]

unifyTypings :: [Map Var (MTy s)] -> M s loc (Map Var (MTy s))
unifyTypings mcs = traverse unifyMany $ zipMaps mcs

unifyMany :: [MTy s] -> M s loc (MTy s)
unifyMany [] = UVar <$> freshVar
unifyMany [t] = return t
unifyMany (t:ts) = do
    foldM (=:=) t ts
    return t

zonkTyping :: MTyping s -> M s loc (MTyping s)
zonkTyping (mc :- t) = do
    mc <- traverse zonk mc
    t <- zonk t
    return $ mc :- t

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps = Map.unionsWith (++) . map (fmap (:[]))

tyInfer :: Term loc -> M s loc (MTyping s)
tyInfer le@(Tagged _ e) = withLoc le $ case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        case vt of
            Just typ -> freshen =<< zonkTyping typ
            Nothing -> throwError $ Err $ unwords ["Not in scope:", show v]
    Con dcon -> do
        ct <- askDataCon dcon
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        return $ mempty :- ct
    Lam v e -> do
        mc :- t <- withMonoVar v $ tyInfer e
        u <- maybe (UVar <$> freshVar) return $ Map.lookup v mc
        return $ Map.delete v mc :- (u ~> t)
    App f e -> do
        mc1 :- t <- tyInfer f
        mc2 :- u <- tyInfer e
        a <- UVar <$> freshVar
        mc <- unifyTypings [mc1, mc2]
        (u ~> a) =:= t
        return $ mc :- a
    Case e as -> do
        mc0 :- t0 <- tyInfer e
        typs <- forM as $ \(pat, e) -> do
            mcPat :- tPat <- tyInferPat pat
            t0 =:= tPat
            mc :- t <- withMonoVars (Map.keys mcPat) $ tyInfer e
            unifyTypings [mc, mcPat]
            let mc' = mc `Map.difference` mcPat
            return $ mc' :- t
        let (mcs, ts) = unzipTypings typs
        mc <- unifyTypings (mc0:mcs)
        t <- unifyMany ts
        return $ mc :- t
    Let binds e -> tyCheckBinds binds $ \mc0 -> do
        mc :- t <- tyInfer e
        mc <- unifyTypings [mc, mc0]
        return $ mc :- t

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
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t) = tFunArgs ct
        unless (length ps == length tArgs) $
          throwError $ Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        typs <- traverse tyInferPat ps
        let (mcs, ts) = unzipTypings typs
        mc <- unifyTypings mcs
        zipWithM_ (=:=) tArgs ts
        return $ mc :- t

tyCheckBinds :: [(Var, Term loc)] -> (Map Var (MTy s) -> M s loc a) -> M s loc a
tyCheckBinds binds body = go mempty $ partitionBinds binds
  where
    go mc0 (bs:bss) = do
        let newVars = map fst bs
        pc <- withMonoVars newVars $ do
            typings <- zip newVars <$> traverse (tyInfer . snd) bs
            let (mcs, ts) = unzipTypings $ map snd typings
                mcRecs = [Map.singleton v t | (v, _ :- t) <- typings]
            unifyTypings (mcs ++ mcRecs)
            let newVarSet = Map.fromList [(v, ()) | v <- newVars]
                unshadow (mc :- t) = (mc `Map.difference` newVarSet) :- t
            return $ fmap unshadow $ Map.fromList typings
        let (mcs, _) = unzipTypings $ Map.elems pc
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: (Pretty loc) => SourceName -> Map DCon PolyTy -> M s loc a -> ST s (Either Doc a)
runM sourceName dataCons = runTC sourceName dataCons Ctx{..}
  where
    polyVars = mempty
