{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Language.HM.Compositional where

import Language.HM.Syntax
import Language.HM.Remap
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty
import Text.Parsec.Pos

import Control.Monad.ST
import Data.STRef
import Control.Unification.Types

import Text.PrettyPrint.HughesPJClass (Doc, Pretty, pPrint)

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

data Typing0 var t v = Map var (UTerm t v) :- (UTerm t v)

deriving instance (Show var, Show v, Show (t (UTerm t v))) => Show (Typing0 var t v)

instance (Functor t) => Functor (Typing0 var t) where
    fmap f (mc :- t) = fmap (fmap f) mc :- fmap f t

instance (Foldable t) => Foldable (Typing0 var t) where
    foldMap f (mc :- t) = foldMap (foldMap f) mc <> foldMap f t

instance (Traversable t) => Traversable (Typing0 var t) where
    traverse f (mc :- t) = (:-) <$> traverse (traverse f) mc <*> traverse f t

type Typing = Typing0 Var Ty0
type MTyping s = Typing (MVar s)

type Err s loc = Tagged (Err0 Ty0 (MVar s)) (loc, Doc)
type UErr s = UFailure Ty0 (MVar s)

data Ctx s loc = Ctx{ polyVars :: Map Var (Maybe (MTyping s))
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

withLoc :: (Pretty src) => Tagged src loc -> M s loc a -> M s loc a
withLoc (Tagged loc src) = local $ \pc -> pc{ loc = (loc, pPrint src) }

withMonoVar :: Var -> M s loc a -> M s loc a
withMonoVar v = withMonoVars [v]

withMonoVars :: [Var] -> M s loc a -> M s loc a
withMonoVars vs = local $ \pc -> pc{ polyVars = Map.union newVars $ polyVars pc }
  where
    newVars = Map.fromList [(v, Nothing) | v <- vs]

withPolyVars :: Map Var (MTyping s) -> M s loc a -> M s loc a
withPolyVars vtys = local $ \pc -> pc{ polyVars = Map.union (Just <$> vtys) $ polyVars pc }

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

unzipTypings :: [Typing0 var t v] -> ([Map var (UTerm t v)], [UTerm t v])
unzipTypings tps = unzip [(mc, t) | mc :- t <- tps]

unifyTypings :: [Map Var (MTy s)] -> M s loc (Map Var (MTy s))
unifyTypings mcs = traverse unifyMany $ zipMaps mcs

unifyMany :: [MTy s] -> M s loc (MTy s)
unifyMany [] = UVar <$> freshVar
unifyMany [t] = return t
unifyMany (t:ts) = do
    foldM (=:=) t ts
    return t

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps = Map.unionsWith (++) . map (fmap (:[]))

instantiateTyping :: MTyping s -> M s loc (MTyping s)
instantiateTyping = instantiate . mono'
  where
    mono' :: MTyping s -> Typing (Either TVar (MVar s))
    mono' = mono

tyInfer :: Term loc -> M s loc (MTyping s)
tyInfer le@(Tagged _ e) = withLoc le $ case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        case vt of
            Just (Just tp) -> instantiateTyping tp
            Just Nothing -> do
                tv <- UVar <$> freshVar
                return $ Map.singleton v tv :- tv
            Nothing -> throwError $ Err $ unwords ["Not in scope:", show v]
    Con dcon -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        return $ mempty :- ct
    Lam v e -> do
        mc :- t <- withMonoVar v $ tyInfer e
        u <- maybe (UVar <$> freshVar) return $ Map.lookup v mc
        return $ Map.delete v mc :- (u ~> t)
    App f e -> do
        mc1 :- t <- tyInfer f
        mc2 :- u <- tyInfer e
        a <- UVar <$> freshVar
        mc <- unifyTypings [mc1, mc2]
        (u ~> a) =:= t
        return $ mc :- a
    Case e as -> do
        mc0 :- t0 <- tyInfer e
        tps <- forM as $ \(pat, e) -> do
            mcPat :- tPat <- tyInferPat pat
            tPat <- t0 =:= tPat
            mc :- t <- withMonoVars (Map.keys mcPat) $ tyInfer e
            unifyTypings [mc, mcPat]
            let mc' = mc `Map.difference` mcPat
            return $ mc' :- t
        let (mcs, ts) = unzipTypings tps
        mc <- unifyTypings (mc0:mcs)
        t <- unifyMany ts
        return $ mc :- t
    Let binds e -> tyCheckBinds binds $ \mc0 -> do
        mc :- t <- tyInfer e
        return $ Map.union mc mc0 :- t

tyInferPat :: Pat loc -> M s loc (MTyping s)
tyInferPat lpat@(Tagged _ pat) = withLoc lpat $ case pat of
    PWild -> do
        t <- UVar <$> freshVar
        return $ mempty :- t
    PVar v -> do
        t <- UVar <$> freshVar
        return $ Map.singleton v t :- t
    PCon dcon ps -> do
        ct <- asks $ Map.lookup dcon . dataCons
        ct <- case ct of
            Nothing -> throwError $ Err $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t) = tFunArgs ct
        unless (length ps == length tArgs) $
          throwError $ Err $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        tps <- traverse tyInferPat ps
        let (mcs, ts) = unzipTypings tps
        mc <- unifyTypings mcs
        zipWithM_ (=:=) tArgs ts
        return $ mc :- t

tyCheckBinds :: [(Var, Term loc)] -> (Map Var (MTy s) -> M s loc a) -> M s loc a
tyCheckBinds binds body = do
    let g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
    go mempty (map flattenSCC $ stronglyConnComp g)
  where
    go mc0 (bs:bss) = do
        pc <- withMonoVars (map fst bs) $ do
            tps <- zip (map fst bs) <$> traverse (tyInfer . snd) bs
            let (mcs, ts) = unzipTypings $ map snd tps
            mc <- unifyTypings mcs
            let mcRecs = [Map.singleton v t | (v, mc :- t) <- tps]
            unifyTypings (mc:mcRecs)
            return $ Map.fromList tps
        let (mcs, _) = unzipTypings $ Map.elems pc
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: (Pretty loc) => SourceName -> Map DCon PolyTy -> M s loc a -> ST s (Either Doc a)
runM sourceName dataCons act = do
    let polyVars = mempty
        pos = initialPos sourceName
    (x, _, _) <- runRWST (runExceptT $ unM act) Ctx{..} 0
    return $ either (Left . pPrint) Right x
