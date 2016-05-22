{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.HM.Meta where

import Language.HM.Syntax
import Language.HM.Remap

import Control.Unification hiding (unify, occursIn, freeVars)
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
import Data.Either
import Data.Function
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)
type MPolyTy s = UTerm Ty0 (Either TVar (MVar s))

instance Ord (STVar s t) where
    compare = compare `on` getVarID

type Subst t v = IntMap (UTerm t v)

subst :: (Traversable t, Variable v) => Subst t v -> UTerm t v -> UTerm t v
subst sub = (>>= substV)
  where
    substV v = maybe (UVar v) (subst sub) $ IntMap.lookup (getVarID v) sub

unify :: (Unifiable t, Variable v)
      => UTerm t v -> UTerm t v -> Either (UFailure t v) (Subst t v)
unify (UVar a)  (UVar b)  | a == b = return mempty
unify (UVar a)  t         = unifyVar a t
unify t         (UVar b)  = unifyVar b t
unify (UTerm t) (UTerm u) = case zipMatch t u of
    Nothing -> Left $ MismatchFailure t u
    Just t' -> foldlM (\sub -> either (keep sub) (roll sub)) mempty t'
  where
    keep sub = const $ return sub
    roll sub (t', u') = (sub <>) <$> unify (subst sub t') (subst sub u')

unifyVar :: (Foldable t, Variable v) => v -> UTerm t v -> Either (UFailure t v) (Subst t v)
unifyVar v t | v `occursIn` t = Left $ OccursFailure v t
             | otherwise = return $ IntMap.singleton (getVarID v) t

varsOf :: (Foldable t) => UTerm t v -> [v]
varsOf (UVar v) = [v]
varsOf (UTerm t) = concatMap varsOf . toList $ t

occursIn :: (Foldable t, Variable v) => v -> UTerm t v -> Bool
v `occursIn` t = v `elem` varsOf t

class (Unifiable t, Variable v, Monad m) => MonadUnify t v m | m t -> v, v m -> t where
    freshVar :: m v

mono :: MTy s -> MPolyTy s
mono = fmap Right

thaw :: PolyTy -> MPolyTy s
thaw = fmap Left

generalizeN :: (Applicative m, Traversable t)
            => m TVar -> (MVar s -> Bool) -> t (MTy s) -> m (t (MPolyTy s))
generalizeN freshTVar free tys = do
    let Pair (Constant mvars) fill = traverse walk tys
    runReader fill <$> traverse (const freshTVar) (Map.fromSet (const ()) mvars)
  where
    walk (UTerm (TApp tcon ts)) = UTerm <$> (TApp tcon <$> traverse walk ts)
    walk (UVar v) | free v = UVar <$> (Left <$> remap v)
                  | otherwise = UVar <$> pure (Right v)

generalize :: (Applicative m) => m TVar -> (MVar s -> Bool) -> MTy s -> m (MPolyTy s)
generalize freshTVar free = fmap runIdentity . generalizeN freshTVar free . Identity

freezePoly :: MPolyTy s -> Maybe PolyTy
freezePoly = walk
  where
    walk (UTerm (TApp tcon ts)) = UTerm <$> (TApp tcon <$> traverse walk ts)
    walk (UVar (Left a)) = UVar <$> pure a
    walk (UVar (Right v)) = mzero

polyMetaVars :: [MPolyTy s] -> Set (MVar s)
polyMetaVars = Set.fromList . snd . partitionEithers . concatMap varsOf

instantiateN :: (MonadUnify Ty0 (MVar s) m, Traversable t)
             => t (MPolyTy s) -> m (t (MTy s))
instantiateN ty = do
    let Pair (Constant tvars) fill = traverse walk ty
    tvars <- traverse (const freshVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
  where
    walk :: MPolyTy s -> Remap TVar (MVar s) (MTy s)
    walk (UTerm (TApp tcon ts)) = UTerm <$> (TApp tcon <$> traverse walk ts)
    walk (UVar (Left a)) = UVar <$> remap a
    walk (UVar (Right v)) = UVar <$> pure v

instantiate :: (MonadUnify Ty0 (MVar s) m)
             => MPolyTy s -> m (MTy s)
instantiate = fmap runIdentity . instantiateN . Identity
