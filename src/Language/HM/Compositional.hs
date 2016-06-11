{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards, TupleSections #-}
{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
module Language.HM.Compositional where

import Language.HM.Monad
import Language.HM.Syntax
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty
import Text.Parsec.Pos

import Control.Monad.ST
import Control.Unification.Types
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Text.PrettyPrint hiding ((<>))
import qualified Text.PrettyPrint.Boxes as Boxes

import Control.Monad.Except
import Control.Monad.RWS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (sort, nub)

data ErrC0 t v = UErrC [(Doc, Typing0 Var t v)] (Maybe Var) (UTerm t v) (UTerm t v) (UFailure t v)
               | BErrC (Doc, Map Var (UTerm t v)) (Doc, Typing0 Var t v) Var (UTerm t v) (UTerm t v) (UFailure t v)
               | ErrC String
deriving instance (Show (t (UTerm t v)), Show v) => Show (ErrC0 t v)

pprErrC :: ErrC0 Ty0 v -> Ppr v Doc
pprErrC (UErrC ucs var t u uerr) = fmap vcat . sequenceA $
    [ flip (<>) colon <$> case var of
          Nothing -> typesPart
          Just v -> fmap sep . sequenceA $
              [ typesPart
              , pure $ text "when unifying"
              , pure $ quotes $ text v
              ]
    , (<+>)
        <$> pprUFailure uerr
        <*> pure (text "in the following context:")
    , text . Boxes.render <$> Boxes.hsep 4 Boxes.top <$> cols
    ]
  where
    typesPart = fmap sep . sequenceA $
      [ pure $ text "Cannot unify", quotes <$> pprType 0 t
      , pure $ text "with"
      , quotes <$> pprType 0 u
      ]

    (vs, mcs') = fillMaps [mc | (_, mc :- t) <- ucs]
    ucs' = zipWith (\(doc, (_ :- t)) vars -> (doc, t, vars)) ucs mcs'
    cols = map (Boxes.vcat Boxes.left) <$> (headerCol:) <$> traverse col ucs'

    headerCol = (Boxes.text ""):(Boxes.text ""):
                [ Boxes.text v Boxes.<+> Boxes.text "::"
                | v <- vs
                ]

    col (doc, t, vars) = sequenceA $
                (pure $ toBox doc):
                (toBox <$> pprType 0 t):
                [ maybe (pure $ Boxes.text "") (fmap toBox . pprType 0) vt
                | (_, vt) <- Map.toList vars
                ]

    toBox = Boxes.text . show

pprErrC (BErrC mc uc var t u uerr) = undefined
pprErrC (ErrC s) = pure $ text s

instance (Ord v, Show v) => Pretty (ErrC0 Ty0 v) where
    pPrintPrec _level _prec = runPpr . pprErrC

type Err s loc = Tagged (ErrC0 Ty0 (MVar s)) (loc, Doc)

data Typing0 var t v = Map var (UTerm t v) :- (UTerm t v)
deriving instance (Show (t (UTerm t v)), Show v, Show var) => Show (Typing0 var t v)

instance (Functor t) => Functor (Typing0 var t) where
    fmap f (mc :- t) = fmap (fmap f) mc :- fmap f t

instance (Foldable t) => Foldable (Typing0 var t) where
    foldMap f (mc :- t) = foldMap (foldMap f) mc <> foldMap f t

instance (Traversable t) => Traversable (Typing0 var t) where
    traverse f (mc :- t) = (:-) <$> traverse (traverse f) mc <*> traverse f t

type Typing = Typing0 Var Ty0
type MTyping s = Typing (MVar s)

data Ctx s loc = Ctx{ polyVars :: Map Var (MTyping s) }

type M s loc = TC (Ctx s loc) (ErrC0 Ty0 (MVar s)) s loc

withMonoVar :: Var -> M s loc a -> M s loc a
withMonoVar v = withMonoVars [v]

withMonoVars :: [Var] -> M s loc a -> M s loc a
withMonoVars vs body = do
    vtys <- traverse monoVar vs
    withPolyVars (Map.fromList vtys) body
  where
    monoVar v = do
        t <- UVar <$> freshVar
        return (v, Map.singleton v t :- t)

withPolyVars :: Map Var (MTyping s) -> M s loc a -> M s loc a
withPolyVars vtys = local $ \pc -> pc{ polyVars = Map.union vtys $ polyVars pc }

unzipTypings :: [Typing0 var t v] -> ([Map var (UTerm t v)], [UTerm t v])
unzipTypings typs = unzip [(mc, t) | mc :- t <- typs]

unifyTypings :: [(Doc, MTyping s)] -> [(MTy s, MTy s)] -> M s loc (Map Var (MTy s))
unifyTypings ucs tyeqs = do
    forM_ tyeqs $ \(t, u) -> runUnify Nothing t u
    flip Map.traverseWithKey (zipMaps mcs) $ \var ts -> case ts of
        [] -> UVar <$> freshVar
        [t] -> return t
        (t:us) -> do
            forM_ ts $ \u -> runUnify (Just var) t u
            return t
  where
    mcs = [mc | (_ , mc :- _) <- ucs]

    runUnify var t u = do
        res <- runExceptT $ unify t u
        case res of
            Left err -> do
                ucs <- traverse (traverse zonkTyping) ucs
                t <- zonk t
                u <- zonk u
                throwError $ UErrC ucs var t u err
            Right ok -> return ok

unifyBindings :: (Doc, Map Var (MTy s)) -> (Doc, MTyping s) -> M s loc (MTyping s)
unifyBindings (docBind, mcBinds) uc = do
    mc <- flip Map.traverseWithKey (zipMaps [mcBinds, mc]) $ \var ts -> case ts of
        [] -> UVar <$> freshVar
        [t] -> return t
        (t:us) -> do
            forM_ ts $ \u -> runUnify var t u
            return t
    return $ mc :- t
  where
    (doc, mc :- t) = uc

    runUnify var t u = do
        res <- runExceptT $ unify t u
        case res of
            Left err -> do
                mcBinds <- traverse zonk mcBinds
                uc <- traverse zonkTyping uc
                t <- zonk t
                u <- zonk u
                throwError $ BErrC (docBind, mcBinds) uc var t u err
            Right ok -> return ok

unifyMany :: [MTy s] -> ExceptT (UFailure Ty0 (MVar s)) (M s loc) (MTy s)
unifyMany [] = UVar <$> lift freshVar
unifyMany [t] = return t
unifyMany (t:ts) = do
    mapM_ (unify t) ts
    return t

zonkTyping :: MTyping s -> M s loc (MTyping s)
zonkTyping (mc :- t) = do
    mc <- traverse zonk mc
    t <- zonk t
    return $ mc :- t

zipMaps :: (Ord k) => [Map k a] -> Map k [a]
zipMaps = Map.unionsWith (++) . map (fmap (:[]))

fillMaps :: (Ord k) => [Map k a] -> ([k], [Map k (Maybe a)])
fillMaps ms = (ks, map fill ms)
  where
    -- TODO: we could do this much more efficient with repeated merging
    ks = nub . sort . concat $ map Map.keys ms

    m0 = Map.fromList [(k, Nothing) | k <- ks]

    fill m = Map.union (Just <$> m) m0

uctx :: (Pretty a) => a -> MTyping s -> (Doc, MTyping s)
uctx e typ = (pPrint e, typ)

tyInfer :: Term loc -> M s loc (MTyping s)
tyInfer le@(Tagged _ e) = withLoc le $ case e of
    Var v -> do
        vt <- asks $ Map.lookup v . polyVars
        case vt of
            Just typ -> freshen =<< zonkTyping typ
            Nothing -> throwError $ ErrC $ unwords ["Not in scope:", show v]
    Con dcon -> do
        ct <- askDataCon dcon
        ct <- case ct of
            Nothing -> throwError $ ErrC $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        return $ mempty :- ct
    Lam v e -> do
        mc :- t <- withMonoVar v $ tyInfer e
        u <- maybe (UVar <$> freshVar) return $ Map.lookup v mc
        return $ Map.delete v mc :- (u ~> t)
    App f e -> do
        typ1@(_ :- t) <- tyInfer f
        typ2@(_ :- u) <- tyInfer e
        a <- UVar <$> freshVar
        mc <- unifyTypings [uctx f typ1, uctx e typ2] [(u ~> a, t)]
        return $ mc :- a
    Case e as -> do
        typ0@(mc0 :- t0) <- tyInfer e
        ucs <- forM as $ \(pat, e) -> do
            typPat@(mcPat :- tPat) <- tyInferPat pat
            typ@(mc :- t) <- withMonoVars (Map.keys mcPat) $ tyInfer e
            unifyTypings [uctx e typ, uctx pat typPat] [(t0, tPat)]
            let mc' = mc `Map.difference` mcPat
            return (pPrintAlt pat e, mc' :- t)
        let (_mcs, ts) = unzipTypings (map snd ucs)
        t <- UVar <$> freshVar
        mc <- unifyTypings (uctx e typ0:ucs) $ map (t,) ts
        return $ mc :- t
    Let binds e -> tyCheckBinds binds $ \mcBinds -> do
        typBody <- tyInfer e
        unifyBindings (bindDoc, mcBinds) (uctx e typBody)
      where
        bindDoc = text "TODO: bindDoc"

tyInferPat :: Pat loc -> M s loc (MTyping s)
tyInferPat lpat@(Tagged _ pat) = withLoc lpat $ case pat of
    PWild -> do
        t <- UVar <$> freshVar
        return $ mempty :- t
    PVar v -> do
        t <- UVar <$> freshVar
        return $ Map.singleton v t :- t
    PCon dcon ps -> do
        ct <- askDataCon dcon
        ct <- case ct of
            Nothing -> throwError $ ErrC $ unwords ["Unknown data constructor:", show dcon]
            Just ct -> instantiate $ thaw ct
        let (tArgs, t) = tFunArgs ct
        unless (length ps == length tArgs) $
          throwError $ ErrC $ unwords ["Bad pattern arity:", show $ length ps, show $ length tArgs]
        typs <- traverse tyInferPat ps
        let ucs = zipWith uctx ps typs
            (_, ts) = unzipTypings typs
        mc <- unifyTypings ucs (zip tArgs ts)
        return $ mc :- t

tyCheckBinds :: [(Var, Term loc)] -> (Map Var (MTy s) -> M s loc a) -> M s loc a
tyCheckBinds binds body = go mempty $ partitionBinds binds
  where
    go mc0 (bs:bss) = do
        let newVars = map fst bs
        pc <- withMonoVars newVars $ do
            typings <- zip newVars <$> traverse (tyInfer . snd) bs
            let (mcs, ts) = unzipTypings $ map snd typings
                typRecs = [Map.singleton v t :- t | (v, _ :- t) <- typings]
                ucs = map (uncurry uctx) typings
                ucRecs = zipWith uctx (map fst bs) typRecs
            unifyTypings (ucs ++ ucRecs) []
            let newVarSet = Map.fromList [(v, ()) | v <- newVars]
                unshadow (mc :- t) = (mc `Map.difference` newVarSet) :- t
            return $ fmap unshadow $ Map.fromList typings
        let (mcs, _) = unzipTypings $ Map.elems pc
        withPolyVars pc $ go (Map.unions (mc0:mcs)) bss
    go mc0 [] = body mc0

runM :: (Pretty loc) => SourceName -> Map DCon PolyTy -> M s loc a -> ST s (Either Doc a)
runM sourceName dataCons = runTC sourceName dataCons Ctx{..}
  where
    polyVars = mempty
