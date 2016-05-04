{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Language.HM.Pretty where

import Language.HM.Syntax
import Language.HM.Remap

import Control.Unification
import Data.Void
import Control.Monad.Reader
import Data.Functor.Product
import Data.Functor.Constant
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream
import Data.List (nub)

type Ppr v = Staged [v] (v -> Doc)

pprVar :: v -> Ppr v Doc
pprVar x = Pair (Constant [x]) (asks ($ x))

pprType :: Rational -> UTerm Ty0 v -> Ppr v Doc
pprType = go
  where
    go p t0@(UTerm t) = case t of
        TApp "Fun" [t, u] -> (\ t u -> par 1 $ t <+> text "->" <+> u) <$> go 1 t <*> go 0 u
        TApp tcon [] -> pure $ text tcon
        TApp tcon targs -> (\ts -> par 2 $ text tcon <+> hsep ts) <$> traverse (go 2) targs
      where
        par i | p >= i = parens
              | otherwise = id
    go p (UVar x) = pprVar x

runPpr :: (Ord v) => Ppr v a -> a
runPpr (Pair (Constant tvars) fill) =
    runReader fill $ \v -> fromJust $ Map.lookup v mapping
  where
    mapping = Map.fromList $ zip (nub tvars) (Stream.toList niceTVars)

niceTVars :: Stream Doc
niceTVars = fmap text $
            Stream.prefix ["α", "β", "c", "d", "e", "f"] $
            fmap (\i -> 'a' : show i) $ Stream.iterate succ 0

instance Pretty Ty where
    pPrintPrec level prec t = pPrintPrec level prec (unfreeze t :: UTerm Ty0 Void)

instance (Eq v, Ord v) => Pretty (UTerm Ty0 v) where
    pPrintPrec level prec t = runPpr $ pprType prec t
