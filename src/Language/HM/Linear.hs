{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Language.HM.Linear where

import Language.HM.Monad
import Language.HM.Syntax
import Language.HM.Meta
import Language.HM.Error
import Text.Parsec.Pos

import Control.Monad.ST
import Control.Unification.Types
import Text.PrettyPrint.HughesPJClass (Doc, Pretty)

import Control.Monad.Except
import Control.Monad.RWS
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

type Err s loc = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)

instance UErr (Err0 t v) t v where
    uerr = UErr

data Ctx s loc = Ctx{ polyVars :: Map Var (MPolyTy s) }

type M s loc = TC (Ctx s loc) (Err0 Ty0 (MVar s)) s loc

withVar :: Var -> MPolyTy s -> M s loc a -> M s loc a
withVar v ty = local $ \pc -> pc{ polyVars = Map.insert v ty $ polyVars pc }

withVars :: Map Var (MPolyTy s) -> M s loc a -> M s loc a
withVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

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
        ct <- askDataCon dcon
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
tyCheckBinds binds body = go $ partitionBinds binds
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
        ct <- askDataCon dcon
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
runM sourceName dataCons = runTC sourceName dataCons Ctx{..}
  where
    polyVars = mempty
