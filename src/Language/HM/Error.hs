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
pprErr (UErr t0 u0 uerr) = header "Type mismatch" $ pprUFailure uerr
  where
    header' s t0' u0' d = hang (text s <> colon) 4 $
                          vcat $ [ text "Expected:" <+> quotes t0'
                                 , text "Got:" <+> quotes u0'
                                 , text ""
                                 , d
                                 ]
    header s d = header' s <$> pprType 0 t0 <*> pprType 0 u0 <*> d
pprErr (Err s) = pure $ text s

instance (Ord v) => Pretty (Err0 Ty0 v) where
    pPrintPrec _level _prec err = runPpr $ pprErr err
