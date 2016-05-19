{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.HM.Meta where

import Language.HM.Syntax
import Language.HM.Remap

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

type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)
type MPolyTy s = UTerm Ty0 (Either TVar (MVar s))

instance Ord (STVar s t) where
    compare = compare `on` getVarID

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
polyMetaVars = execWriter . traverse_ go
  where
    go (UTerm (TApp _ ts)) = traverse_ go ts
    go (UVar (Left a)) = pure ()
    go (UVar (Right v)) = tell $ Set.singleton v

instantiateN :: (BindingMonad Ty0 (MVar s) m, Traversable t)
             => t (MPolyTy s) -> m (t (MTy s))
instantiateN ty = do
    let Pair (Constant tvars) fill = traverse walk ty
    tvars <- traverse (const freeVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
  where
    walk :: MPolyTy s -> Remap TVar (MVar s) (MTy s)
    walk (UTerm (TApp tcon ts)) = UTerm <$> (TApp tcon <$> traverse walk ts)
    walk (UVar (Left a)) = UVar <$> remap a
    walk (UVar (Right v)) = UVar <$> pure v

instantiate :: (BindingMonad Ty0 (MVar s) m)
             => MPolyTy s -> m (MTy s)
instantiate = fmap runIdentity . instantiateN . Identity

(~>) :: UTerm Ty0 v -> UTerm Ty0 v -> UTerm Ty0 v
t ~> u = UTerm $ TApp "Fun" [t, u]

infixr 7 ~>
