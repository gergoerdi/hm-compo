{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

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

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

{-
instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u
-}

pprErr :: Err0 Ty0 v -> Ppr v Doc
pprErr (UErr t0 u0 uerr) = case uerr of
    OccursFailure v t ->
        header "Infinite type" <$> sequenceA [pprVar v, pprType 0 t]
    MismatchFailure t u ->
        header "Type mismatch" <$> sequenceA [ (text "Expected:" <+>) <$> pprType0 0 t
                                             , (text "Got:" <+>) <$> pprType0 0 u]
  where
    header s = hang (text s <> colon) 4 . vcat
pprErr (Err s) = pure $ text s

instance (Ord v) => Pretty (Err0 Ty0 v) where
    pPrintPrec _level _prec err = runPpr $ pprErr err
