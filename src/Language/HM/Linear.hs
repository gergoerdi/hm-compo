{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
module Language.HM.Linear where

import Language.HM.Syntax
import Language.HM.Remap
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty
import Text.Parsec.Pos

import Control.Monad.ST
import Data.STRef
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

type Err s loc = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)
type UErr s = UFailure Ty0 (MVar s)

data Ctx s loc = Ctx{ polyVars :: Map Var (MPolyTy s)
                    , dataCons :: Map DCon PolyTy
                    , loc :: (loc, Doc)
                    }

newtype M s loc a = M{ unM :: ExceptT (Err s loc) (RWST (Ctx s loc) () Int (ST s)) a }
                  deriving ( Functor, Applicative, Monad
                           , MonadReader (Ctx s loc)
                           , MonadState Int
                           )

instance MonadError (Err0 Ty0 (MVar s)) (M s loc) where
    throwError err = do
        loc <- asks loc
        M . throwError $ Tagged loc err
    catchError act handler = M $ catchError (unM act) (unM . handler . unTag)

instance MonadTC Ty0 (MVar s) (M s loc) where
    freshVar = do
        id <- state $ \i -> (i, succ i)
        ref <- M . lift . lift $ newSTRef Nothing
        return $ STVar id ref
    readVar (STVar _ ref) = M . lift . lift $ readSTRef ref
    writeVar (STVar _ ref) t = M . lift . lift $ writeSTRef ref $ Just t

infix 4 =:=
(=:=) :: MTy s -> MTy s -> M s loc (MTy s)
t =:= u = do
    res <- runExceptT $ unify t u
    case res of
        Left uerr -> do
            t <- zonk t
            u <- zonk u
            throwError $ UErr t u uerr
        Right () -> return t

withVar :: Var -> MPolyTy s -> M s loc a -> M s loc a
withVar v ty = local $ \pc -> pc{ polyVars = Map.insert v ty $ polyVars pc }

withVars :: Map Var (MPolyTy s) -> M s loc a -> M s loc a
withVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

withLoc :: (Pretty src) => Tagged src loc -> M s loc a -> M s loc a
withLoc (Tagged loc src) = local $ \pc -> pc{ loc = (loc, pPrint src) }

freshTVar :: M s loc TVar
freshTVar = get <* modify succ

generalizeHere :: [MTy s] -> M s loc [MPolyTy s]
generalizeHere tys = do
    tysInScope <- asks $ Map.elems . polyVars
    tvsInScope <- Set.fromList <$> getMetaVarsN tysInScope
    let free = (`Set.notMember` tvsInScope)
    generalizeN freshTVar free =<< traverse zonk tys

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
    App f e -> do
        t' <- UVar <$> freshVar
        tyCheck (t' ~> t) f
        tyCheck t' e
        return t
    Case e as -> do
        t0 <- tyInfer e
        forM as $ \(pat, e) ->
          tyCheckPat t0 pat $ tyCheck t e
        return t
    Let binds e -> tyCheckBinds binds $ tyCheck t e

tyCheckBinds :: [(Var, Term loc)] -> M s loc a -> M s loc a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go (map flattenSCC $ stronglyConnComp g)
  where
    go (bs:bss) = do
        tvs <- traverse (const $ UVar <$> freshVar) bs
        tvs <- withVars (Map.fromList $ zip (map fst bs) (map mono tvs)) $
          zipWithM tyCheck tvs (map snd bs)
        ts <- generalizeHere tvs
        withVars (Map.fromList $ map fst bs `zip` ts) $ go bss
    go [] = body

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
        t =:= t0
        unless (length ps == length tArgs) $
          throwError . Err $
            unwords [ "Bad pattern arity:"
                    , show $ length ps
                    , show $ length tArgs
                    ]
        go (zip tArgs ps)
      where
        go ((t, p):tps) = tyCheckPat t p $ go tps
        go [] = body

tyInfer :: Term loc -> M s loc (MTy s)
tyInfer e = do
    ty <- UVar <$> freshVar
    tyCheck ty e

runM :: (Pretty loc) => SourceName -> Map DCon PolyTy -> M s loc a -> ST s (Either Doc a)
runM sourceName dataCons act = do
    let polyVars = mempty
        pos = initialPos sourceName
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
