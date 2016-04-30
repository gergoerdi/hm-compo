{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Language.HM.Pretty where

import Language.HM.Syntax
import Language.HM.Remap

import Control.Unification
import Data.Void
import Control.Monad.Reader
import Control.Monad.Writer hiding (Product)
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass
import Data.Stream (Stream(..))
import qualified Data.Stream as Stream
import Data.List (nub)

instance Pretty Ty where
    pPrintPrec level prec t = pPrintPrec level prec (unfreeze t :: UTerm Ty0 Void)

niceTVars :: Stream String
niceTVars = Stream.prefix ["α", "β", "c", "d", "e", "f"] $
            fmap (\i -> 'a' : show i) $ Stream.iterate succ 0

instance (Eq v, Ord v) => Pretty (UTerm Ty0 v) where
    pPrintPrec level prec t = case go prec t of
        Pair (Constant tvars) fill ->
            runReader fill $ Map.fromList $ zip (nub tvars) (Stream.toList niceTVars)
      where
        go p t0@(UTerm t) = case t of
            TApp{} -> case tApps t0 of
                (UTerm (TCon "Fun"), [t, u]) ->
                    (\ t u -> par 1 $ t <+> text "->" <+> u) <$> go 1 t <*> go 0 u
                (tcon, []) -> go 0 tcon
                (tcon, targs) -> (\t ts -> par 2 $ t <+> hsep ts) <$> go 0 tcon <*> traverse (go 2) targs
            TCon tcon -> pure $ text tcon
          where
            par i | p >= i = parens
                  | otherwise = id
        go p (UVar a) = text <$> remap a

        remap x = Pair (Constant [x]) (asks $ fromJust . Map.lookup x)
