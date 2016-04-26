{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

import Data.Foldable
import Data.Traversable
import Data.Functor.Fixedpoint
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Control.Monad.RWS hiding (Product)
import Control.Monad.Reader
import Control.Monad.Trans.Identity
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass

data TyF tcon tv r
    = TVar tv
    | TApp r r
    | TCon tcon
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq tcon, Eq tv) => Unifiable (TyF tcon tv) where
    zipMatch (TCon dc1) (TCon dc2) = do
        guard $ dc1 == dc2
        return $ TCon dc1
    zipMatch (t1 `TApp` t2) (t1' `TApp` t2') = do
        return $ Right (t1, t1') `TApp` Right (t2, t2')
    zipMatch (TVar alpha) (TVar beta) = do
        guard $ alpha == beta
        return $ TVar alpha
    zipMatch _ _ = mzero

type TCon = String
type TVar = String
type Ty0 = TyF TCon TVar

type Ty = Fix Ty0
type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)

type Err s = UFailure Ty0 (MVar s)

tApps :: Ty -> (Ty, [Ty])
tApps t = case go t of
    (t, ts) -> (t, reverse ts)
  where
    go (Fix (TApp t u)) = case go t of (t, ts) -> (t, u:ts)
    go t = (t, [])

tApps' :: MTy s -> (MTy s, [MTy s])
tApps' t = case go t of
    (t, ts) -> (t, reverse ts)
  where
    go (UTerm (TApp t u)) = case go t of (t, ts) -> (t, u:ts)
    go t = (t, [])

instance Pretty Ty where
    pPrintPrec level = go
      where
        go p t0@(Fix t) = case t of
            TApp{} -> case tApps t0 of
                (Fix (TCon "Fun"), [t, u]) -> par 1 $ go 1 t <+> text "->" <+> go 0 u
                (tcon, []) -> go 0 tcon
                (tcon, targs) -> par 2 $ go 0 tcon <+> hsep (map (go 2) targs)
            TVar tv -> text tv
            TCon tcon -> text tcon
          where
            par i | p >= i = parens
                  | otherwise = id

instance Pretty (MTy s) where
    pPrintPrec level prec t = case go prec t of
        Pair (Constant tvars) fill -> runReader fill $ Map.fromAscList $ zip (Set.toAscList tvars) [1..]
      where
        go :: Rational -> MTy s -> Remap Int Int Doc
        go p t0@(UTerm t) = case t of
            TApp{} -> case tApps' t0 of
                (UTerm (TCon "Fun"), [t, u]) ->
                    (\ t u -> par 1 $ t <+> text "->" <+> u) <$> go 1 t <*> go 0 u
                (tcon, []) -> go 0 tcon
                (tcon, targs) -> (\t ts -> par 2 $ t <+> hsep ts) <$> go 0 tcon <*> traverse (go 2) targs
            TVar tv -> pure $ text tv
            TCon tcon -> pure $ text tcon
          where
            par i | p >= i = parens
                  | otherwise = id
        go p (UVar v) = (\i -> text $ 't' : show i) <$> remap (getVarID v)

-- pprMTy :: MTy s -> Doc
-- pprMTy

newtype M s a = M{ unM :: ExceptT (Err s) (RWST () () Int (STBinding s)) a }
              deriving (Functor, Applicative, Monad)

-- instance PrettyM (M s) (MTy s)

instance BindingMonad Ty0 (MVar s) (M s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

instance MonadError (Err s) (M s) where
    throwError = M . throwError
    catchError (M act) = M . catchError act . (unM .)

type Staged w r = Product (Constant w) (Reader r)
type Remap from to = Staged (Set from) (Map from to)

remap :: (Ord from) => from -> Remap from to to
remap x = Pair (Constant (Set.singleton x)) (asks $ fromJust . Map.lookup x)

instantiate :: forall s. (TVar -> Bool) -> MTy s -> M s (MTy s)
instantiate free ty = do
    let Pair (Constant tvars) fill = walk ty
    tvars <- traverse (const freeVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
  where
    walk :: MTy s -> Remap TVar (MVar s) (MTy s)
    walk (UTerm (TVar alpha))
      | free alpha = Pair (Constant $ Set.singleton alpha) (asks $ UVar . fromJust . Map.lookup alpha)
      | otherwise = UTerm <$> pure (TVar alpha)

    walk (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk t <*> walk u)
    walk (UTerm (TCon con)) = UTerm <$> pure (TCon con)
    walk (UVar a) = UVar <$> pure a

t `tTo` u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u

foo :: forall s. M s (MTy s)
foo = do
    let ta = UTerm $ TVar "a"
        tb = UTerm $ TVar "b"
        tList t = UTerm $ (UTerm $ TCon "List") `TApp` t
    let tMapPoly = (ta `tTo` tb) `tTo` (tList ta `tTo` tList tb)

    let tInt = UTerm $ TCon "Int"
        tMaybe t = UTerm $ (UTerm $ TCon "Maybe") `TApp` t
        tMapMono = (tInt `tTo` tMaybe tInt) `tTo` (tList tInt `tTo` tList (tMaybe tInt))

    tMapPoly' <- instantiate (const True) tMapPoly
    -- tv <- UVar <$> freeVar
    t2 <- runIdentityT $ tMapMono =:= tMapPoly'
    t2 <- runIdentityT $ applyBindings t2
    return $ tMapPoly'
    -- return $ freeze tMapPoly

foo' :: forall s. M s Doc
foo' = do
    -- mt <- foo
    -- case mt of
    --     Nothing -> return $ text "<err>"
    --     Just t -> return $ pPrint t
    pPrint <$> foo

-- runM :: (forall s. M s a) -> Either String a
-- runM act = runSTBinding $ do
--     (x, _, _) <- runRWST (runExceptT $ unM act) () 0
--     return $ bimap show id x

-- runM :: M s a -> STBinding s (Either (Err s) a)
-- runM act = do
--     (x, _, _) <- runRWST (runExceptT $ unM act) () 0
--     return x

runM :: M s a -> STBinding s a
runM act = do
    (x, _, _) <- runRWST (runExceptT $ unM act) () 0
    return $ either (error . show) id x
