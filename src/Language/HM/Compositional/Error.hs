{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards, TupleSections #-}
module Language.HM.Compositional.Error where

import Language.HM.Syntax
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty

import Control.Unification.Types
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Text.PrettyPrint hiding ((<>))
import qualified Text.PrettyPrint.Boxes as Boxes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (sort, nub)
import Data.Monoid ((<>))

data Typing0 var t v = Map var (UTerm t v) :- (UTerm t v)

data ErrC0 t v = UErrC [(Doc, Typing0 Var t v)] (Maybe Var) (UTerm t v) (UTerm t v) (UFailure t v)
               | BErrC (Map Var (UTerm t v)) (Doc, Typing0 Var t v) Var (UTerm t v) (UTerm t v) (UFailure t v)
               | ErrC String

pprErrTypes :: UTerm Ty0 v -> UTerm Ty0 v -> Ppr v Doc
pprErrTypes t u = fmap sep . sequenceA $
    [ pure $ text "Cannot unify", quotes <$> pprType 0 t
    , pure $ text "with"
    , quotes <$> pprType 0 u
    ]

pprErrC :: ErrC0 Ty0 v -> Ppr v Doc
pprErrC (UErrC ucs var t u uerr) = fmap vcat . sequenceA $
    [ flip (<>) colon <$> case var of
          Nothing -> pprErrTypes t u
          Just v -> fmap sep . sequenceA $
              [ pprErrTypes t u
              , pure $ text "when unifying"
              , pure $ quotes $ text v
              ]
    , fmap sep . sequenceA $
      [ pprUFailure uerr
      , pure (text "in the following context:")
      ]
    , text . Boxes.render <$> Boxes.hsep 4 Boxes.top <$> cols
    ]
  where
    (vs, mcs') = fillMaps [mc | (_, mc :- t) <- ucs]
    ucs' = zipWith (\(doc, (_ :- t)) vars -> (doc, t, vars)) ucs mcs'
    cols = (:) <$> headerCol <*> traverse col ucs'

    headerCol = column mempty Nothing $
        map (\v -> pure $ text v <+> dcolon) vs

    col (doc, t, vars) = column doc (Just t) $
        map (maybe (pure mempty) (pprType 0)) (Map.elems vars)
pprErrC (BErrC mc uc var t u uerr) = fmap vcat . sequenceA $
    [ fmap ((<> colon) . hsep) . sequenceA $
      [ pprErrTypes t u
      , pure $ text "when unifying"
      , pure $ quotes $ text var
      ]
    , fmap sep . sequenceA $
      [ pprUFailure uerr
      , pure (text "in the following context:")
      ]
    , text . Boxes.render <$> Boxes.hsep 4 Boxes.top <$> cols
    ]
  where
    (doc, mc' :- t) = uc
    vs = Map.keys mc

    cols = sequenceA $ [headerCol, bindingsCol, bodyCol]

    headerCol = column mempty Nothing $
        map (\v -> pure $ text v <+> dcolon) vs

    bindingsCol = column (text "Let-bound variables") Nothing $
        map (pprType 0) (Map.elems mc)

    bodyCol = column doc (Just t) $
        [ maybe (pure mempty) (pprType 0) vt
        | v <- vs
        , let vt = Map.lookup v mc'
        ]
pprErrC (ErrC s) = pure $ text s

column :: Doc -> Maybe (UTerm Ty0 v) -> [Ppr v Doc] -> Ppr v Boxes.Box
column doc t vars = fmap (Boxes.vcat Boxes.left) . sequenceA $
    pure (toBox doc):
    maybe (pure nilBox) (fmap toBox . pprType 0) t:
    map (fmap toBox) vars

nilBox :: Boxes.Box
nilBox = Boxes.text ""

toBox :: Doc -> Boxes.Box
toBox = Boxes.text . show

instance (Ord v) => Pretty (ErrC0 Ty0 v) where
    pPrintPrec _level _prec = runPpr . pprErrC

instance (Functor t) => Functor (Typing0 var t) where
    fmap f (mc :- t) = fmap (fmap f) mc :- fmap f t

instance (Foldable t) => Foldable (Typing0 var t) where
    foldMap f (mc :- t) = foldMap (foldMap f) mc <> foldMap f t

instance (Traversable t) => Traversable (Typing0 var t) where
    traverse f (mc :- t) = (:-) <$> traverse (traverse f) mc <*> traverse f t

fillMaps :: (Ord k) => [Map k a] -> ([k], [Map k (Maybe a)])
fillMaps ms = (ks, map fill ms)
  where
    -- TODO: we could do this much more efficient with repeated merging
    ks = nub . sort . concat $ map Map.keys ms

    m0 = Map.fromList [(k, Nothing) | k <- ks]

    fill m = Map.union (Just <$> m) m0
