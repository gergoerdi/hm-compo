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

data Err0 t v = UErr (UFailure t v)
              | Err String

deriving instance (Show v, Show (t (UTerm t v))) => Show (Err0 t v)

instance Fallible t v (Err0 t v) where
    occursFailure v t = UErr $ occursFailure v t
    mismatchFailure t u = UErr $ mismatchFailure t u

pprErr :: Err0 Ty0 v -> Ppr v Doc
pprErr err = case err of
    UErr (OccursFailure v t) ->
        header "Infinite type" <$> sequenceA [pprVar v, pprType 0 t]
    UErr (MismatchFailure t u) ->
        header "Type mismatch" <$> sequenceA [pprType0 0 t, pprType0 0 u]
    Err s -> pure $ text s
  where
    header s = hang (text s <> colon) 4 . vcat

instance (Ord v) => Pretty (Err0 Ty0 v) where
    pPrintPrec _level _prec err = runPpr $ pprErr err
