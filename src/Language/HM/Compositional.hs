{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards, TupleSections #-}

module Language.HM.Compositional where

import Language.HM.Syntax
import Language.HM.Remap
import Language.HM.Meta

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

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

import Debug.Trace

data Typing0 var ty = Map var ty :- ty

type Typing = Typing0 Var Ty
type MTyping s = Typing0 Var (MTy s)

data Err0 t v = UErr (UFailure t v)
              | Err String

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

type Err s = Err0 Ty0 (MVar s)

instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u

data Ctx s = Ctx{ polyVars :: Map Var (Maybe (MTyping s))
                , dataCons :: Map DCon PolyTy
                }

newtype M s a = M{ unM :: ExceptT (Err s) (RWST (Ctx s) () Int (STBinding s)) a }
              deriving (Functor, Applicative, Monad, MonadReader (Ctx s), MonadState Int)

withMonoVar :: Var -> M s a -> M s a
withMonoVar v = withMonoVars [v]

withMonoVars :: [Var] -> M s a -> M s a
withMonoVars vs = local $ \pc -> pc{ polyVars = Map.union newVars $ polyVars pc }
  where
    newVars = Map.fromList [(v, Nothing) | v <- vs]

withPolyVars :: Map Var (MTyping s) -> M s a -> M s a
withPolyVars vtys = local $ \pc -> pc{ polyVars = Map.union (Just <$> vtys) $ polyVars pc }

instance BindingMonad Ty0 (MVar s) (M s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

{-
instance PolyBindingMonad Ty0 (MVar s) (Err s) (M s) where
    freshTVar = get <* modify succ

    getIsFree = do
        tysInScope <- asks $ Map.elems . polyVars
        let tvsInScope = polyMetaVars tysInScope
        return $ (`Set.notMember` tvsInScope)
-}

-- unifyTyping :: [Map Var (MTy s)] -> [MTy s] -> M s (MTyping s)
-- unifyTyping mcs ts = do
--     traverse_ unifyMany $ zipMaps mcs
--     unifyMany ts
--     -- mc <- runIdentityT $ applyBindingsAll $ Map.unions mcs
--     -- t <- runIdentityT $ applyBindings t
--     let mc = Map.unions mcs
--     traceShow (mc, t) $ return ()
--     return $ mc :- t

unifyTypings :: [Map Var (MTy s)] -> M s (Map Var (MTy s))
unifyTypings mcs = do
    traverse_ unifyMany $ zipMaps mcs
    -- mc <- runIdentityT $ applyBindingsAll $ Map.unions mcs
    return $ Map.unions mcs

unifyMany :: [MTy s] -> M s ()
unifyMany [t] = return ()
unifyMany (t:ts) = void $ runIdentityT $ foldM (=:=) t ts

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps [] = mempty
zipMaps (m:ms) = foldr (Map.intersectionWith (:)) (pure <$> m) ms

instantiateTyping :: MTyping s -> M s (MTyping s)
instantiateTyping = error "instantiateTyping"

instance MonadError (Err s) (M s) where
    throwError = M . throwError
    catchError (M act) = M . catchError act . (unM .)

tyInfer :: Term -> M s (MTyping s)
tyInfer e = case unFix e of
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
        runIdentityT $ (u ~> a) =:= t
        return $ mc :- a
    Case e as -> do
        undefined
        -- t0 <- tyInfer e
        -- forM_ as $ \(pat, e) -> do
        --     tyCheckPat t0 pat $ tyCheck t e
    Let binds e -> tyCheckBinds binds $ \mc0 -> do
        mc :- e <- tyInfer e
        return $ Map.union mc mc0 :- e

tyCheckBinds :: [(Var, Term)] -> (Map Var (MTy s) -> M s a) -> M s a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go mempty (map flattenSCC $ stronglyConnComp g)
  where
    go mc0 (bs:bss) = do
        pc <- withMonoVars (map fst bs) $ do
            tps <- zip (map fst bs) <$> traverse (tyInfer . snd) bs
            let mcs = [Map.insert v t mc | (v, mc :- t) <- tps]
            unifyTypings mcs
            return $ Map.fromList tps
        let mcs = [mc | (mc :- t) <- Map.elems pc]
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: Map DCon PolyTy -> M s a -> STBinding s a
runM dataCons act = do
    let polyVars = mempty
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (error . show) id x
