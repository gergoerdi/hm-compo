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
               | BErrC (Doc, Map Var (UTerm t v)) (Doc, Typing0 Var t v) Var (UTerm t v) (UTerm t v) (UFailure t v)
               | ErrC String

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
