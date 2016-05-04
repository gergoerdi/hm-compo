{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Language.HM.Linear where

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

data Err0 t v = UErr (UFailure t v)
              | Err String

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

type Err s = Err0 Ty0 (MVar s)

instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u

data Ctx s = Ctx{ polyVars :: Map Var (MPolyTy s)
                , dataCons :: Map DCon PolyTy
                }

newtype M s a = M{ unM :: ExceptT (Err s) (RWST (Ctx s) () Int (STBinding s)) a }
              deriving (Functor, Applicative, Monad, MonadReader (Ctx s), MonadState Int)

withVar :: Var -> MPolyTy s -> M s a -> M s a
withVar v ty = local $ \pc -> pc{ polyVars = Map.insert v ty $ polyVars pc }

withVars :: Map Var (MPolyTy s) -> M s a -> M s a
withVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

instance BindingMonad Ty0 (MVar s) (M s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

instance MonadError (Err s) (M s) where
    throwError = M . throwError
    catchError (M act) = M . catchError act . (unM .)

freshTVar :: M s TVar
freshTVar = get <* modify succ

generalise :: (Traversable t) => t (MTy s) -> M s (t (MPolyTy s))
generalise tys = do
    tys <- runIdentityT $ applyBindingsAll tys
    tysInScope <- asks $ Map.elems . polyVars
    let tvsInScope = polyMetaVars tysInScope
        free = (`Set.notMember` tvsInScope)
    let Pair (Constant mvars) fill = traverse (walk free) tys
    runReader fill <$> traverse (const freshTVar) (Map.fromSet (const ()) mvars)
  where
    walk :: (MVar s -> Bool) -> MTy s -> Remap (MVar s) TVar (MPolyTy s)
    walk free (UTerm (TApp tcon ts)) = UTerm <$> (TApp tcon <$> traverse (walk free) ts)
    walk free (UVar v) | free v = UVar <$> (Left <$> remap v)
                       | otherwise = UVar <$> pure (Right v)

tyCheck :: MTy s -> Term tag -> M s ()
tyCheck t e = case unTag e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        vt <- case vt of
            Nothing -> throwError $ Err $ unwords ["Not in scope:", show v]
            Just t -> instantiate t
        runIdentityT $ vt =:= t
        return ()
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        runIdentityT $ ct =:= t
        return ()
    Lam v e -> do
        t0 <- UVar <$> freeVar
        withVar v (mono t0) $ do
            u <- tyInfer e
            runIdentityT $ t0 ~> u =:= t
        return ()
    App f e -> do
        t1 <- tyInfer f
        t2 <- tyInfer e
        runIdentityT $ t1 =:= t2 ~> t
        return ()
    Case e as -> do
        t0 <- tyInfer e
        forM_ as $ \(pat, e) -> do
            tyCheckPat t0 pat $ tyCheck t e
    Let binds e -> tyCheckBinds binds $ tyCheck t e

tyCheckBinds :: [(Var, Term tag)] -> M s a -> M s a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go (map flattenSCC $ stronglyConnComp g)
  where
    go (bs:bss) = do
        tvs <- traverse (const $ UVar <$> freeVar) bs
        withVars (Map.fromList $ zip (map fst bs) (map mono tvs)) $
          zipWithM_ tyCheck tvs (map snd bs)
        ts <- generalise tvs
        withVars (Map.fromList $ map fst bs `zip` ts) $ go bss
    go [] = body

tyCheckPat :: MTy s -> Pat tag -> M s a -> M s a
tyCheckPat t p body = case unTag p of
    PWild -> body
    PVar v -> withVar v (mono t) body
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t0) = tFunArgs ct
        runIdentityT $ t =:= t0
        unless (length ps == length tArgs) $
          throwError $ Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        go (zip tArgs ps)
      where
        go ((t, p):tps) = tyCheckPat t p $ go tps
        go [] = body

tyInfer :: Term a -> M s (MTy s)
tyInfer e = do
    ty <- UVar <$> freeVar
    tyCheck ty e
    return ty

runM :: Map DCon PolyTy -> M s a -> STBinding s a
runM dataCons act = do
    let polyVars = mempty
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (error . show) id x
