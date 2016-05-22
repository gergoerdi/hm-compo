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
import Language.HM.Error
import Language.HM.Pretty
import Text.Parsec.Pos

-- import Control.Unification hiding ((=:=), (=~=))
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

import Debug.Trace

type Err s loc = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)
type UErr s = UFailure Ty0 (MVar s)

data Ctx s loc = Ctx{ polyVars :: Map Var (MPolyTy s)
                    , dataCons :: Map DCon PolyTy
                    , loc :: (loc, Doc)
                    }

newtype M s loc a = M{ unM :: ExceptT (Err s loc) (RWST (Ctx s loc) () Int (STBinding s)) a }
                  deriving ( Functor, Applicative, Monad
                           , MonadReader (Ctx s loc)
                           , MonadState Int
                           -- , MonadError (Err s loc)
                           )

instance MonadError (Err0 Ty0 (MVar s)) (M s loc) where
    throwError err = do
        loc <- asks loc
        M . throwError $ Tagged loc err
    catchError act handler = M $ catchError (unM act) (unM . handler . unTag)

infix 4 =:=
(=:=) :: MTy s -> MTy s -> M s loc (MTy s)
t =:= u = do
    sub <- t =~= u
    return $ subst sub t

infix 4 =~=
(=~=) :: MTy s -> MTy s -> M s loc (Subst Ty0 (MVar s))
t =~= u = case unify t u of
    Left uerr -> throwError $ UErr t u uerr
    Right sub -> return sub

withVar :: Var -> MPolyTy s -> M s loc a -> M s loc a
withVar v ty = local $ \pc -> pc{ polyVars = Map.insert v ty $ polyVars pc }

withVars :: Map Var (MPolyTy s) -> M s loc a -> M s loc a
withVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

withLoc :: (Pretty src) => Tagged src loc -> M s loc a -> M s loc a
withLoc (Tagged loc src) = local $ \pc -> pc{ loc = (loc, pPrint src) }

instance MonadUnify Ty0 (MVar s) (M s loc) where
    freshVar = M . lift . lift $ freeVar

freshTVar :: M s loc TVar
freshTVar = get <* modify succ

generalizeHere :: [MTy s] -> M s loc [MPolyTy s]
generalizeHere tys = do
    tysInScope <- asks $ Map.elems . polyVars
    let tvsInScope = polyMetaVars tysInScope
        free = (`Set.notMember` tvsInScope)
    generalizeN freshTVar free tys

tyCheck :: MTy s -> Term loc -> M s loc (MTy s)
tyCheck t le@(Tagged _ e) = withLoc le $ case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        vt <- case vt of
            Nothing -> throwError . Err $
                         unwords ["Not in scope:", show v]
            Just t -> instantiate t
        vt =:= t
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError . Err $
                         unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        ct =:= t
    Lam v e -> do
        t0 <- UVar <$> freshVar
        withVar v (mono t0) $ do
            u <- tyInfer e
            t0 ~> u =:= t
    -- App f e -> do
    --     t1 <- tyInfer f
    --     t2 <- tyInfer e
    --     runFatal le $ t1 =:= t2 ~> t
    --     t1 <- runInternal $ applyBindings t1
    --     t2 <- runInternal $ applyBindings t2
    --     t <- runInternal $ applyBindings t
    --     traceShow (t1, t2, t) $ return ()
    --     -- runInternal $ applyBindings t
    --     return t
    -- Case e as -> do
    --     t0 <- tyInfer e
    --     ts <- forM as $ \(pat, e) -> do
    --         tyCheckPat t0 pat $ tyCheck t e
    --     return $ case ts of
    --         (t':_) -> t'
    --         _ -> t
    -- Let binds e -> tyCheckBinds binds $ tyCheck t e

{-
tyCheckBinds :: [(Var, Term loc)] -> M s loc a -> M s loc a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go (map flattenSCC $ stronglyConnComp g)
  where
    go (bs:bss) = do
        tvs <- traverse (const $ UVar <$> freeVar) bs
        tvs <- withVars (Map.fromList $ zip (map fst bs) (map mono tvs)) $
          zipWithM tyCheck tvs (map snd bs)
        ts <- generalizeHere tvs
        withVars (Map.fromList $ map fst bs `zip` ts) $ go bss
    go [] = body
-}

tyCheckPat :: MTy s -> Pat loc -> M s loc a -> M s loc a
tyCheckPat t lp@(Tagged tag p) body = case p of
    PWild -> body
    PVar v -> withVar v (mono t) body
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError . Err $
                         unwords [ "Unknown data constructor:"
                                 , show dcon
                                 ]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t0) = tFunArgs ct
        sub <- t =~= t0
        unless (length ps == length tArgs) $
          throwError . Err $
            unwords [ "Bad pattern arity:"
                    , show $ length ps
                    , show $ length tArgs
                    ]
        tArgs <- return $ fmap (subst sub) tArgs
        go (zip tArgs ps)
      where
        go ((t, p):tps) = tyCheckPat t p $ go tps
        go [] = body

tyInfer :: Term loc -> M s loc (MTy s)
tyInfer e = do
    ty <- UVar <$> freshVar
    tyCheck ty e

runM :: (Pretty loc)
     => Map DCon PolyTy
     -> M s loc a
     -> STBinding s (Either Doc a)
runM dataCons act = do
    let polyVars = mempty
        pos = initialPos "foo"
        -- loc = (pos, empty)
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (Left . pPrintErr) Right $ x
  where
    pPrintErr (Tagged (loc, src) err) =
        vcat [ pPrint loc
             , nest 4 src
             , text ""
             , pPrint err
             ]
