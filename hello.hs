{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

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

import Debug.Trace

data TyF tcon k
    = TApp k k
    | TCon tcon
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq tcon) => Unifiable (TyF tcon) where
    zipMatch (TCon dc1) (TCon dc2) = do
        guard $ dc1 == dc2
        return $ TCon dc1
    zipMatch (t1 `TApp` t2) (t1' `TApp` t2') = do
        return $ Right (t1, t1') `TApp` Right (t2, t2')
    zipMatch _ _ = mzero

type TCon = String
type TVar = String
type Ty0 = TyF TCon

type Ty = Fix Ty0
type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)
type MPolyTy s = (Set (MVar s), MTy s)

instance Ord (STVar s t) where
    compare = compare `on` getVarID

data Err0 t v = UErr (UFailure t v)
              | Err String

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

type Err s = Err0 Ty0 (MVar s)

instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u

mono :: MTy s -> MPolyTy s
mono ty = (mempty, ty)

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

tFunArgs :: MTy s -> ([MTy s], MTy s)
tFunArgs = go
  where
    go (UTerm (TApp (UTerm (TApp (UTerm (TCon "Fun")) t)) u)) =
        case go u of (ts, t0) -> (t:ts, t0)
    go t = ([], t)

instance Pretty Ty where
    pPrintPrec level = go
      where
        go p t0@(Fix t) = case t of
            TApp{} -> case tApps t0 of
                (Fix (TCon "Fun"), [t, u]) -> par 1 $ go 1 t <+> text "->" <+> go 0 u
                (tcon, []) -> go 0 tcon
                (tcon, targs) -> par 2 $ go 0 tcon <+> hsep (map (go 2) targs)
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
            TCon tcon -> pure $ text tcon
          where
            par i | p >= i = parens
                  | otherwise = id
        go p (UVar v) = (\i -> text $ 't' : show i) <$> remap (getVarID v)

data Term0 dcon var
    = Var var
    | Con dcon
    | Lam var (Term0 dcon var)
    | App (Term0 dcon var) (Term0 dcon var)
    | Case (Term0 dcon var) [(Pat0 dcon var, Term0 dcon var)]
    | Let [(var, Term0 dcon var)] (Term0 dcon var)
    deriving Show

infixl 7 `App`

data Pat0 dcon var
    = PVar var
    | PWild
    | PCon dcon [Pat0 dcon var]
    deriving Show

type Var = String
type DCon = String

type Term = Term0 DCon Var
type Pat = Pat0 DCon Var

data PCtx s = PCtx{ polyVars :: Map Var (MPolyTy s)
                  , dataCons :: Map DCon (MTy s)
                  }

newtype M s a = M{ unM :: ExceptT (Err s) (RWST (PCtx s) () () (STBinding s)) a }
              deriving (Functor, Applicative, Monad, MonadReader (PCtx s))

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

type Staged w r = Product (Constant w) (Reader r)
type Remap from to = Staged (Set from) (Map from to)

remap :: (Ord from) => from -> Remap from to to
remap x = Pair (Constant (Set.singleton x)) (asks $ fromJust . Map.lookup x)

instantiate :: forall s. (MVar s -> Bool) -> MTy s -> M s (MTy s)
instantiate free ty = do
    ty <- runIdentityT $ applyBindings ty
    let Pair (Constant tvars) fill = walk ty
    tvars <- traverse (const freeVar) $ Map.fromSet (const ()) tvars
    return $ runReader fill tvars
  where
    walk :: MTy s -> Remap (MVar s) (MVar s) (MTy s)
    walk (UTerm (TApp t u)) = UTerm <$> (TApp <$> walk t <*> walk u)
    walk (UTerm (TCon con)) = UTerm <$> pure (TCon con)
    walk (UVar a)
      | free a = UVar <$> remap a
      | otherwise = UVar <$> pure a

t `tTo` u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u

tyCheck :: MTy s -> Term -> M s ()
tyCheck t e = case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        vt <- case vt of
            Nothing -> throwError $ Err $ unwords ["Not in scope:", show v]
            Just (fvs, t) -> instantiate (`Set.member` fvs) t
        runIdentityT $ vt =:= t
        return ()
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> return ct
        ct <- instantiate (const True) ct
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
    Let binds e -> do
        let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
        go (map flattenSCC $ stronglyConnComp g)
      where
        go (bs:bss) = do
            tvs <- traverse (const $ UVar <$> freeVar) bs
            withVars (Map.fromList $ zip (map fst bs) (map mono tvs)) $
              zipWithM_ tyCheck tvs (map snd bs)
            tysInScope <- asks $ Map.elems . polyVars
            tvsInScope <- fmap (Set.fromList . concat) $ traverse (getFreeVars . snd) tysInScope
            traceShow "go" $ return ()
            ts <- forM (bs `zip` tvs) $ \((v, _), t) -> do
                fvs <- (Set.\\ tvsInScope) . Set.fromList <$> getFreeVars t
                return (v, (fvs, t))
            withVars (Map.fromList ts) $ go bss
        go [] = tyCheck t e

freeVarsOfTerm :: Term -> Set Var
freeVarsOfTerm = execWriter . go
  where
    go (Var v) = tell $ Set.singleton v
    go (Lam v e) = censor (Set.delete v) $ go e
    go Con{} = return ()
    go (App f e) = go f >> go e
    go (Case e as) = go e >> traverse_ alt as
    go (Let bs e) = do
        let bounds = Set.fromList $ map fst bs
        censor (Set.\\ bounds) $ do
            traverse_ (go . snd) bs
            go e

    alt (p, e) = censor (Set.\\ freeVarsOfPat p) $ go e

freeVarsOfPat :: Pat -> Set Var
freeVarsOfPat = execWriter . go
  where
    go PWild = return ()
    go (PVar v) = tell $ Set.singleton v
    go (PCon _ ps) = traverse_ go ps

tyCheckPat :: MTy s -> Pat -> M s a -> M s a
tyCheckPat t p body = case p of
    PWild -> body
    PVar v -> withVar v (mono t) body
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> return ct
        ct <- instantiate (const True) ct
        let (tArgs, t0) = tFunArgs ct
        runIdentityT $ t =:= t0
        unless (length ps == length tArgs) $
          throwError $ Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs, show $ pPrint ct]
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
    alpha <- UVar <$> freeVar
    beta <- UVar <$> freeVar
    let polyVars = mempty
        dataCons = Map.fromList [ ("Nil", tList alpha)
                                , ("Cons", alpha ~> (tList alpha ~> tList alpha))
                                , ("MkPair", alpha ~> (beta ~> tPair alpha beta))
                                ]
          where
            t ~> u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Fun") t) u
            tList = UTerm . TApp (UTerm $ TCon "List")
            tPair t u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Pair") t) u
    (x, _, _) <- runRWST (runExceptT $ unM act) PCtx{..} ()
    return $ either (error . show) id x

foo :: M s Doc
foo = do
    t <- tyInfer e'
    t <- runIdentityT $ applyBindings t
    return $ pPrint t
  where
    e = Lam "f" $ Lam "xs" $ Case (Var "xs")
          [ (PCon "Nil" [], Con "Nil")
          , (PCon "Cons" [PVar "x", PVar "xs"],
             (Con "Cons" `App` (Var "f" `App` Var "x")) `App` (Var "xs"))
          ]

    e' = Let [("map", Lam "f" $ Lam "xs" $ Case (Var "xs")
                        [ (PCon "Nil" [], Con "Nil")
                        , (PCon "Cons" [PVar "x", PVar "xs"],
                           Con "Cons" `App` (Var "f" `App` Var "x") `App`
                           (Var "map" `App` Var "f" `App` Var "xs"))
                        ])]
           (Con "MkPair" `App` Var "map" `App` Var "map")
