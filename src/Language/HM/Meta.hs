{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Language.HM.Meta where

import Language.HM.Syntax
import Language.HM.Remap

import Control.Unification hiding (unify, occursIn, freeVars)
import Control.Unification.Types
import Data.STRef

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

import Debug.Trace

data STVar s t = STVar Int (STRef s (Maybe (UTerm t (STVar s t))))
type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)
type MPolyTy s = UTerm Ty0 (Either TVar (MVar s))

instance Variable (STVar s t) where
    getVarID (STVar id _) = id

instance Show (STVar s t) where
    show (STVar id _) = "v" <> show id

instance Eq (STVar s t) where
    (==) = (==) `on` getVarID

instance Ord (STVar s t) where
    compare = compare `on` getVarID

type Subst t v = IntMap (UTerm t v)

class (Show (UTerm t v), Show v, Unifiable t, Variable v, Monad m) => MonadTC t v m | m t -> v, v m -> t where
    freshVar :: m v
    readVar :: v -> m (Maybe (UTerm t v))
    writeVar :: v -> UTerm t v -> m ()

unify :: (MonadTC t v m) => UTerm t v -> UTerm t v -> ExceptT (UFailure t v) m ()
unify (UVar a)  (UVar b) | a == b = return ()
unify (UVar a)  t        = unifyVar a t
unify t         (UVar b) = unifyVar b t
unify (UTerm t) (UTerm u) = case zipMatch t u of
    Nothing -> throwError $ MismatchFailure t u
    Just t' -> traverse_ (either (const $ pure ()) (uncurry unify)) t'

unifyVar :: (MonadTC t v m) => v -> UTerm t v -> ExceptT (UFailure t v) m ()
unifyVar v t = do
    deref <- lift $ readVar v
    -- traceShow ("unifyVar", v, t, deref) $ return ()
    case deref of
        Just u -> unify u t
        Nothing -> unifyUnbound
  where
    unifyUnbound = case t of
        UVar v' -> do
            deref' <- lift $ readVar v'
            case deref' of
                Just u -> unify (UVar v) u
                Nothing -> lift $ writeVar v t
        UTerm u -> do
            checkOccurs u
            lift $ writeVar v t

    checkOccurs u = do
        vs <- lift $ getMetaVars u
        when (v `elem` vs) $ do
            t' <- lift $ zonk t
            throwError $ OccursFailure v t'

class (MonadTC t v m) => HasMetaVars t v m a where
    getMetaVars :: a -> m [v]

instance (MonadTC t v m) => HasMetaVars t v m (UTerm t v) where
    getMetaVars = getMetaVarsN

instance (MonadTC t v m) => HasMetaVars t v m (t (UTerm t v)) where
    getMetaVars = getMetaVarsN

instance (MonadTC t v m) => HasMetaVars t v m (UTerm t (Either tv v)) where
    getMetaVars = getMetaVarsN . snd . partitionEithers . toList

instance (MonadTC t v m) => HasMetaVars t v m v where
    getMetaVars v = do
        t <- zonkVar v
        case t of
            UVar v -> return [v]
            UTerm t -> getMetaVars t

getMetaVarsN :: (HasMetaVars t v m a, Foldable f) => f a -> m [v]
getMetaVarsN = fmap concat . traverse getMetaVars . toList

zonk :: (Traversable t, MonadTC t v m) => UTerm t v -> m (UTerm t v)
zonk (UTerm t) = UTerm <$> traverse zonk t
zonk (UVar v) = zonkVar v

zonkVar :: (Traversable t, MonadTC t v m) => v -> m (UTerm t v)
zonkVar v = do
    deref <- readVar v
    case deref of
        Nothing -> return $ UVar v
        Just t -> do
            t' <- zonk t
            writeVar v t'
            return t'

zonkPoly :: (Traversable t, MonadTC t v m) => UTerm t (Either tv v) -> m (UTerm t (Either tv v))
zonkPoly (UVar (Left a)) = return $ UVar (Left a)
zonkPoly (UVar (Right v)) = fmap Right <$> zonkVar v
zonkPoly (UTerm t) = UTerm <$> traverse zonkPoly t

mono :: (Functor f) => f v -> f (Either tv v)
mono = fmap Right

thaw :: PolyTy -> MPolyTy s
thaw = fmap Left

generalizeN :: (Monad m, Variable v, Traversable t, Traversable f)
            => m tv -> (v -> Bool) -> f (UTerm t v) -> m (f (UTerm t (Either tv v)))
generalizeN freshTVar free tys = do
    let Pair (Constant mvars) fill = traverse (traverse walk) tys
    runReader fill <$> traverse (const freshTVar) (Map.fromSet (const ()) mvars)
  where
    walk v | free v = Left <$> remap (getVarID v)
           | otherwise = pure (Right v)

generalize :: (Variable v, Traversable t, Monad m) => m tv -> (v -> Bool) -> UTerm t v -> m (UTerm t (Either tv v))
generalize freshTVar free = fmap runIdentity . generalizeN freshTVar free . Identity

freezePoly :: MPolyTy s -> Maybe PolyTy
freezePoly = traverse (either pure (const mzero))

instantiate :: (Ord tv, MonadTC t v m, Traversable f) => f (Either tv v) -> m (f v)
instantiate ptys = do
    let Pair (Constant tvars) fill = traverse (either remap pure) ptys
    tvars <- traverse (const freshVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
