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

freezePoly :: MPolyTy s -> Maybe PolyTy
freezePoly = walk
  where
    walk (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk t <*> walk u)
    walk (UTerm (TCon tcon)) = UTerm <$> pure (TCon tcon)
    walk (UVar (Left a)) = UVar <$> pure a
    walk (UVar (Right v)) = mzero

polyMetaVars :: [MPolyTy s] -> Set (MVar s)
polyMetaVars = execWriter . traverse_ go
  where
    go (UTerm (TApp t u)) = go t >> go u
    go (UTerm (TCon _)) = pure ()
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
    walk (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk t <*> walk u)
    walk (UTerm (TCon con)) = UTerm <$> pure (TCon con)
    walk (UVar (Left a)) = UVar <$> remap a
    walk (UVar (Right v)) = UVar <$> pure v

instantiate :: (BindingMonad Ty0 (MVar s) m)
             => MPolyTy s -> m (MTy s)
instantiate = fmap runIdentity . instantiateN . Identity

(~>) :: UTerm Ty0 v -> UTerm Ty0 v -> UTerm Ty0 v
t ~> u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u

infixr 7 ~>
