{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Language.HM.Pretty where

import Language.HM.Syntax
import Language.HM.Remap
import Language.Haskell.Exts (SrcSpanInfo, SrcLoc(..), ParseResult(..), getPointLoc)

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

pprType0 :: Rational -> Ty0 (UTerm Ty0 v) -> Ppr v Doc
pprType0 = go
  where
    go p t = case t of
        TFun t u -> (\ t u -> par 1 $ t <+> text "→" <+> u) <$> pprType 1 t <*> pprType 0 u
        TApp tcon [] -> pure $ text tcon
        TApp tcon targs -> (\ts -> par 2 $ text tcon <+> hsep ts) <$> traverse (pprType 2) targs
      where
        par i | p >= i = parens
              | otherwise = id

pprType :: Rational -> UTerm Ty0 v -> Ppr v Doc
pprType p (UTerm t) = pprType0 p t
pprType p (UVar x) = pprVar x

runPpr :: (Ord v) => Ppr v a -> a
runPpr (Pair (Constant tvars) fill) =
    runReader fill $ \v -> fromJust $ Map.lookup v mapping
  where
    mapping = Map.fromList $ zip (nub tvars) (Stream.toList niceTVars)

niceTVars :: Stream Doc
niceTVars = fmap text $
            Stream.prefix ["a", "b", "c", "d", "e", "f"] $
            -- Stream.prefix ["α", "β", "c", "d", "e", "f"] $
            fmap (\i -> 'a' : show i) $ Stream.iterate succ 0

instance Pretty Ty where
    pPrintPrec level prec t = pPrintPrec level prec (unfreeze t :: UTerm Ty0 Void)

instance (Ord v) => Pretty (UTerm Ty0 v) where
    pPrintPrec level prec t = runPpr $ pprType prec t

instance Pretty (PatF String String a) where
    pPrintPrec level prec p = case p of
        PVar x -> text x
        PWild -> text "_"
        PCon dcon pats -> maybeParens (not (null pats) && prec >= 1) $
                          text dcon <+> hsep (map (pPrintPrec level (prec + 1)) pats)

instance Pretty (TermF String String a) where
    pPrintPrec level prec p = case p of
        Var x -> text x
        Con dcon -> text dcon
        Lam var e -> maybeParens (prec >= 1) $
                     text "\\" <> text var <+> text "->" <+> pPrintPrec level prec e
        App f e -> maybeParens (prec >= 1) $
                   pPrintPrec level 0 f <+> pPrintPrec level 1 e
        Case e alts -> hang (text "case" <+> pPrintPrec level prec e <+> text "of") 2
                       (vcat (map (uncurry pPrintAlt) alts))
        Let es f -> vcat [ text "let" <+> (vcat (map pPrintVar es))
                         , text "in" <+> pPrintPrec level prec f
                         ]

pPrintVar :: (String, Term0 String String a) -> Doc
pPrintVar (v, e) = text v <+> text "=" <+> pPrint e

pPrintAlt :: Pat0 String String loc -> Term0 String String loc -> Doc
pPrintAlt p e = pPrint p <+> text "->" <+> pPrint e

instance (Pretty a) => Pretty (Tagged a tag) where
    pPrintPrec level prec = pPrintPrec level prec . unTag

instance Pretty SrcLoc where
    pPrint SrcLoc{..} =
        text srcFilename <+> parens coords <> colon
      where
        coords = int srcLine <> comma <> int srcColumn

instance Pretty SrcSpanInfo where
    pPrint = pPrint . getPointLoc

dcolon :: Doc
dcolon = text "::"
