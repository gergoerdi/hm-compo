{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Language.HM.Linear where

import Language.HM.Syntax
import Language.HM.Pretty
import Language.HM.Remap

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

import Data.Foldable
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS hiding (Product)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Product)
import Control.Monad.Trans.Identity
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Graph
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass
import Data.Function

type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)
type MPolyTy s = UTerm Ty0 (Either TVar (MVar s))

instance Ord (STVar s t) where
    compare = compare `on` getVarID

data Err0 t v = UErr (UFailure t v)
              | Err String

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

type Err s = Err0 Ty0 (MVar s)

instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u

data PCtx s = PCtx{ polyVars :: Map Var (MPolyTy s)
                  -- , tvarSupply :: Stream TVar
                  , dataCons :: Map DCon PolyTy
                  }

newtype M s a = M{ unM :: ExceptT (Err s) (RWST (PCtx s) () Int (STBinding s)) a }
              deriving (Functor, Applicative, Monad, MonadReader (PCtx s), MonadState Int)

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

fresh :: M s TVar
fresh = get <* modify succ

polyMetaVars :: [MPolyTy s] -> Set (MVar s)
polyMetaVars = execWriter . traverse_ go
  where
    go (UTerm (TApp t u)) = go t >> go u
    go (UTerm (TCon _)) = pure ()
    go (UVar (Left a)) = pure ()
    go (UVar (Right v)) = tell $ Set.singleton v

generalise :: forall s a. [MTy s] -> M s [MPolyTy s]
generalise tys = do
    tys <- runIdentityT $ applyBindingsAll tys
    tysInScope <- asks $ Map.elems . polyVars
    -- tvsInScope <- undefined -- fmap (Set.fromList . concat . map lefts) $ traverse getFreeVars tysInScope
    let tvsInScope = polyMetaVars tysInScope
    let Pair (Constant mvars) fill = traverse (walk (`Set.notMember` tvsInScope)) tys
    runReader fill <$> traverse (const fresh) (Map.fromSet (const ()) mvars)
  where
    walk :: (MVar s -> Bool) -> MTy s -> Remap (MVar s) TVar (MPolyTy s)
    walk free (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk free t <*> walk free u)
    walk free (UTerm (TCon con)) = UTerm <$> pure (TCon con)
    walk free (UVar v) | free v = UVar <$> (Left <$> remap v)
                       | otherwise = UVar <$> pure (Right v)

instantiate :: forall s. MPolyTy s -> M s (MTy s)
instantiate ty = do
    let Pair (Constant tvars) fill = walk ty
    tvars <- traverse (const freeVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
  where
    walk :: MPolyTy s -> Remap TVar (MVar s) (MTy s)
    walk (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk t <*> walk u)
    walk (UTerm (TCon con)) = UTerm <$> pure (TCon con)
    walk (UVar (Left a)) = UVar <$> remap a
    walk (UVar (Right v)) = UVar <$> pure v

t `tTo` u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u

tyCheck :: MTy s -> Term -> M s ()
tyCheck t e = case e of
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
            runIdentityT $ (t0 `tTo` u) =:= t
        return ()
    App f e -> do
        t1 <- tyInfer f
        t2 <- tyInfer e
        runIdentityT $ t1 =:= t2 `tTo` t
        return ()
    Case e as -> do
        t0 <- tyInfer e
        forM_ as $ \(pat, e) -> do
            tyCheckPat t0 pat $ tyCheck t e
    Let binds e -> tyCheckBinds binds $ tyCheck t e

tyCheckBinds :: [(Var, Term)] -> M s a -> M s a
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

tyCheckPat :: MTy s -> Pat -> M s a -> M s a
tyCheckPat t p body = case p of
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

tyInfer :: Term -> M s (MTy s)
tyInfer e = do
    ty <- UVar <$> freeVar
    tyCheck ty e
    return ty

runM :: M s a -> STBinding s a
runM act = do
    let polyVars = mempty
        dataCons = Map.fromList [ ("Nil", tList alpha)
                                , ("Cons", alpha ~> (tList alpha ~> tList alpha))
                                , ("MkPair", alpha ~> (beta ~> tPair alpha beta))
                                ]
          where
            alpha = UVar (-1)
            beta = UVar (-2)
            t ~> u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u
            tList = UTerm . TApp (UTerm $ TCon "List")
            tPair t u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Pair") t) u
    (x, _, _) <- runRWST (runExceptT $ unM act) PCtx{..} 0
    return $ either (error . show) id x

dcolon :: Doc
dcolon = text "::"

foo :: M s Doc
foo = do
    pvars <- foo'
    return $ vcat [ text name <+> dcolon <+> pPrint t
                  | (name, t) <- Map.toList pvars
                  ]

foo' :: M s (Map Var PolyTy)
foo' = do
    tyCheckBinds bs $ do
        pvars <- asks polyVars
        return $ fromMaybe (error "metavar escaped to top level!") $
          traverse freezePoly pvars
  where
    bs = [ ("map", Lam "f" $ Lam "xs" $ Case (Var "xs")
                   [ (PCon "Nil" [], Con "Nil")
                   , (PCon "Cons" [PVar "x", PVar "xs"],
                      Con "Cons" `App` (Var "f" `App` Var "x") `App`
                      (Var "map" `App` Var "f" `App` Var "xs"))
                   ])
         , ("foldr", Lam "f" $ Lam "y" $ Lam "xs" $ Case (Var "xs")
                     [ (PCon "Nil" [], Var "y")
                     , (PCon "Cons" [PVar "x", PVar "xs"],
                        Var "f" `App` Var "x" `App` (Var "foldr" `App` Var "f" `App` Var "y" `App` Var "xs"))
                     ])
         ]
