{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Language.HM.Error where

import Language.HM.Syntax
import Language.HM.Pretty

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass

data Err0 t v = UErr (UTerm t v) (UTerm t v) (UFailure t v)
              | Err String

pprUFailure :: UFailure Ty0 v -> Ppr v Doc
pprUFailure (OccursFailure v t) = fmap hsep . sequenceA $
    [ pure $ text "Infinite type in"
    , quotes <$> pprVar v
    , pure $ text "~"
    , quotes <$> pprType 0 t
    ]
pprUFailure (MismatchFailure t u) = fmap hsep . sequenceA $
    [ (text "Cannot unify" <+>) <$> quotes <$> pprType0 0 t
    , (text "with" <+>) <$> quotes <$> pprType0 0 u
    ]

pprErr :: Err0 Ty0 v -> Ppr v Doc
pprErr (UErr t u uerr) =
    header "Type mismatch" <$>
      pprType 0 t <*>
      pprType 0 u <*>
      pprUFailure uerr
  where
    header s t' u' d = hang (text s <> colon) 4 $
                       vcat $ [ text "Expected:" <+> quotes t'
                              , text "Got:" <+> quotes u'
                              , text ""
                              , d
                              ]
pprErr (Err s) = pure $ text s

instance (Ord v) => Pretty (Err0 Ty0 v) where
    pPrintPrec _level _prec err = runPpr $ pprErr err
