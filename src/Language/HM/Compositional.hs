{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards, TupleSections #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Language.HM.Compositional where

import Language.HM.Syntax
import Language.HM.Remap
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass

import Data.Foldable
import Data.Functor.Fixedpoint
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS hiding (Product)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Product)
import Control.Monad.Identity
import Control.Monad.Trans.Identity
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Graph
import Data.Maybe
import Data.Function

data Typing0 var ty = Map var ty :- ty
                    deriving (Show, Functor, Foldable, Traversable)

type Typing = Typing0 Var Ty
type MTyping s = Typing0 Var (MTy s)

type Err tag s = Err0 Ty0 (MVar s)

data Ctx s = Ctx{ polyVars :: Map Var (Maybe (MTyping s))
                , dataCons :: Map DCon PolyTy
                }

newtype M tag s a = M{ unM :: ExceptT (Err tag s) (RWST (Ctx s) () Int (STBinding s)) a }
                  deriving (Functor, Applicative, Monad, MonadReader (Ctx s), MonadState Int)

runFatal :: IdentityT (M tag s) a -> M tag s a
runFatal = runIdentityT

withMonoVar :: Var -> M tag s a -> M tag s a
withMonoVar v = withMonoVars [v]

withMonoVars :: [Var] -> M tag s a -> M tag s a
withMonoVars vs = local $ \pc -> pc{ polyVars = Map.union newVars $ polyVars pc }
  where
    newVars = Map.fromList [(v, Nothing) | v <- vs]

withPolyVars :: Map Var (MTyping s) -> M tag s a -> M tag s a
withPolyVars vtys = local $ \pc -> pc{ polyVars = Map.union (Just <$> vtys) $ polyVars pc }

unzipTypings :: [Typing0 var ty] -> ([Map var ty], [ty])
unzipTypings tps = unzip [(mc, t) | mc :- t <- tps]

instance BindingMonad Ty0 (MVar s) (M tag s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

unifyTypings :: [Map Var (MTy s)] -> M tag s (Map Var (MTy s))
unifyTypings mcs = runIdentityT $ do
    traverse unifyMany $ zipMaps mcs
    -- return $ Map.unions mcs

unifyMany :: [MTy s] -> IdentityT (M tag s) (MTy s)
unifyMany [] = UVar <$> lift freeVar
unifyMany [t] = return t
unifyMany (t:ts) = do
    foldM (=:=) t ts
    return t

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps = Map.unionsWith (++) . map (fmap (:[]))

instantiateTyping :: MTyping s -> M tag s (MTyping s)
instantiateTyping = runFatal . freshenAll

instance MonadError (Err tag s) (M tag s) where
    throwError = M . throwError
    catchError (M act) = M . catchError act . (unM .)

tyInfer :: Term tag -> M tag s (MTyping s)
tyInfer (Tagged tag e) = case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        case vt of
            Just (Just tp) -> instantiateTyping tp
            Just Nothing -> do
                tv <- UVar <$> freeVar
                return $ Map.singleton v tv :- tv
            Nothing -> throwError $ Err $ unwords ["Not in scope:", show v]
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        return $ mempty :- ct
    Lam v e -> do
        mc :- t <- withMonoVar v $ tyInfer e
        u <- maybe (UVar <$> freeVar) return $ Map.lookup v mc
        return $ Map.delete v mc :- (u ~> t)
    App f e -> do
        mc1 :- t <- tyInfer f
        mc2 :- u <- tyInfer e
        a <- UVar <$> freeVar
        mc <- unifyTypings [mc1, mc2]
        runFatal $ (u ~> a) =:= t
        return $ mc :- a
    Case e as -> do
        mc0 :- t0 <- tyInfer e
        tps <- forM as $ \(pat, e) -> do
            mcPat :- tPat <- tyInferPat pat
            tPat <- runFatal $ t0 =:= tPat
            mc :- t <- withMonoVars (Map.keys mcPat) $ tyInfer e
            unifyTypings [mc, mcPat]
            let mc' = mc `Map.difference` mcPat
            return $ mc' :- t
        let (mcs, ts) = unzipTypings tps
        mc <- unifyTypings (mc0:mcs)
        t <- runFatal $ unifyMany ts
        return $ mc :- t
    Let binds e -> tyCheckBinds binds $ \mc0 -> do
        mc :- t <- tyInfer e
        return $ Map.union mc mc0 :- t

tyInferPat :: Pat tag -> M tag s (MTyping s)
tyInferPat pat = case unTag pat of
    PWild -> do
        t <- UVar <$> freeVar
        return $ mempty :- t
    PVar v -> do
        t <- UVar <$> freeVar
        return $ Map.singleton v t :- t
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t) = tFunArgs ct
        unless (length ps == length tArgs) $
          throwError $ Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        tps <- traverse tyInferPat ps
        let (mcs, ts) = unzipTypings tps
        mc <- unifyTypings mcs
        runFatal $ zipWithM_ (=:=) tArgs ts
        return $ mc :- t

tyCheckBinds :: [(Var, Term tag)] -> (Map Var (MTy s) -> M tag s a) -> M tag s a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go mempty (map flattenSCC $ stronglyConnComp g)
  where
    go mc0 (bs:bss) = do
        pc <- withMonoVars (map fst bs) $ do
            tps <- zip (map fst bs) <$> traverse (tyInfer . snd) bs
            -- let mcs = [Map.insert v t mc | (v, mc :- t) <- tps]
            -- unifyTypings mcs
            let (mcs, ts) = unzipTypings $ map snd tps
            mc <- unifyTypings mcs
            let mcRecs = [Map.singleton v t | (v, mc :- t) <- tps]
            unifyTypings (mc:mcRecs)
            return $ Map.fromList tps
        let (mcs, _) = unzipTypings $ Map.elems pc
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: Map DCon PolyTy -> M tag s a -> STBinding s (Either Doc a)
runM dataCons act = do
    let polyVars = mempty
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (Left . pPrint) Right x
