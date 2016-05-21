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

import Control.Unification
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

type Err loc s = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)
type UErr s = UFailure Ty0 (MVar s)

data Ctx s = Ctx{ polyVars :: Map Var (MPolyTy s)
                , dataCons :: Map DCon PolyTy
                }

newtype M loc s a = M{ unM :: ExceptT (Err loc s) (RWST (Ctx s) () Int (STBinding s)) a }
                  deriving ( Functor, Applicative, Monad
                           , MonadReader (Ctx s)
                           , MonadState Int
                           , MonadError (Err loc s)
                           )

infix 4 =::=
(=::=) :: (BindingMonad t v m, Fallible t v e, MonadTrans em, Functor (em m), MonadError e (em m))
       => UTerm t v
       -> UTerm t v
       -> em m (UTerm t v)
(=::=) = unifyOccurs

runFatal :: (Pretty b)
         => Tagged b loc
         -> ExceptT (UErr s) (STBinding s) (MTy s)
         -> M loc s (MTy s)
runFatal (Tagged loc src) act = do
    result <- M . lift . lift $ runExceptT $ applyBindings =<< act
    case result of
        Left err -> do
            err' <- runInternal $ case err of
                OccursFailure v t ->
                    OccursFailure v <$> applyBindings t
                MismatchFailure t u ->
                    MismatchFailure <$> applyBindingsAll t <*> applyBindingsAll u
            throwError $ Tagged (loc, pPrint src) $ UErr err'
        Right x -> return x

runInternal :: ExceptT (UErr s) (STBinding s) a -> M loc s a
runInternal act = do
    result <- M . lift . lift $ runExceptT act
    case result of
        Left err -> error "Internal error"
        Right x -> return x

withVar :: Var -> MPolyTy s -> M loc s a -> M loc s a
withVar v ty = local $ \pc -> pc{ polyVars = Map.insert v ty $ polyVars pc }

withVars :: Map Var (MPolyTy s) -> M loc s a -> M loc s a
withVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

instance BindingMonad Ty0 (MVar s) (M loc s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

freshTVar :: M loc s TVar
freshTVar = get <* modify succ

-- generalizeHere :: (Traversable t) => t (MTy s) -> M loc s (t (MPolyTy s))
generalizeHere :: [MTy s] -> M loc s [MPolyTy s]
generalizeHere tys = do
    tys <- runInternal $ applyBindingsAll tys
    traceShow tys $ return ()
    -- tys <- traverse semiprune tys
    tysInScope <- asks $ Map.elems . polyVars
    tysInScope <- traverse applyBindingsPoly tysInScope
    let tvsInScope = polyMetaVars tysInScope
        free = (`Set.notMember` tvsInScope)

    pvars <- asks polyVars
    traceShow pvars $ return ()

    generalizeN freshTVar free tys
    -- generalizeN freshTVar (const False) tys

tyCheck :: MTy s -> Term loc -> M loc s (MTy s)
tyCheck t le@(Tagged loc e) = case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        vt <- case vt of
            Nothing -> throwError $ Tagged (loc, pPrint e) $
                         Err $ unwords ["Not in scope:", show v]
            Just t -> instantiate t
        runFatal le $ vt =::= t
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Tagged (loc, pPrint e) $
                         Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        runFatal le $ ct =::= t
    Lam v e -> do
        t0 <- UVar <$> freeVar
        withVar v (mono t0) $ do
            u <- tyInfer e
            runFatal le $ t0 ~> u =::= t
    App f e -> do
        t1 <- tyInfer f
        t2 <- tyInfer e
        runFatal le $ t1 =::= t2 ~> t
        -- runInternal $ applyBindings t
        return t
    Case e as -> do
        t0 <- tyInfer e
        ts <- forM as $ \(pat, e) -> do
            tyCheckPat t0 pat $ tyCheck t e
        return $ case ts of
            (t':_) -> t'
            _ -> t
    Let binds e -> tyCheckBinds binds $ tyCheck t e

tyCheckBinds :: [(Var, Term loc)] -> M loc s a -> M loc s a
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

tyCheckPat :: MTy s -> Pat loc -> M loc s a -> M loc s a
tyCheckPat t lp@(Tagged tag p) body = case p of
    PWild -> body
    PVar v -> withVar v (mono t) body
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Tagged (tag, pPrint p) $
                         Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t0) = tFunArgs ct
        runFatal lp $ t =::= t0
        unless (length ps == length tArgs) $
          throwError $ Tagged (tag, pPrint p) $
            Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        go (zip tArgs ps)
      where
        go ((t, p):tps) = tyCheckPat t p $ go tps
        go [] = body

tyInfer :: Term loc -> M loc s (MTy s)
tyInfer e = do
    ty <- UVar <$> freeVar
    tyCheck ty e

runM :: (Pretty loc)
     => Map DCon PolyTy
     -> M loc s a
     -> STBinding s (Either Doc a)
runM dataCons act = do
    let polyVars = mempty
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (Left . pPrintErr) Right $ x
  where
    pPrintErr (Tagged (loc, src) err) =
        vcat [ pPrint loc
             , nest 4 src
             , text ""
             , pPrint err
             ]
