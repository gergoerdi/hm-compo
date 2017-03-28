{-# LANGUAGE RecordWildCards #-}
module Language.HM.Parser
       ( parseSource, Decl(..)
       , SrcSpanInfo(..), SrcLoc(..), HSE.getPointLoc
       ) where

import Language.HM.Syntax
import Language.HM.Pretty

import Control.Unification
import Data.Functor.Fixedpoint
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (forM)

import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass

import Language.Haskell.Exts.Parser
import Language.Haskell.Exts (SrcSpanInfo, SrcLoc, ParseResult(..))
import qualified Language.Haskell.Exts as HSE

data Decl tag = DataDef DCon PolyTy
              | VarDef Var (Term tag)
              deriving Show


type ParseError = (SrcLoc, String)

parseSource :: FilePath -> String -> Either Doc [Decl SrcSpanInfo]
parseSource sourceName s = case fromModule =<< parseModuleWithMode mode s of
    ParseOk decls -> Right decls
    ParseFailed loc err -> Left $ pPrint loc $$ text err
  where
    mode = HSE.defaultParseMode{ HSE.parseFilename = sourceName }

err :: (HSE.SrcInfo loc, HSE.Annotated ast) => ast loc -> ParseResult a
err ast = ParseFailed (HSE.getPointLoc . HSE.ann $ ast) "Unsupported Haskell syntax"

fromModule :: (HSE.SrcInfo loc) => HSE.Module loc -> ParseResult [Decl loc]
fromModule (HSE.Module _ Nothing [] [] decls) = concat <$> mapM fromDecl decls
fromModule mod = err mod

fromName :: (HSE.SrcInfo loc) => HSE.Name loc -> ParseResult String
fromName (HSE.Ident _ var) = return var
fromName name = err name

fromQName :: (HSE.SrcInfo loc) => HSE.QName loc -> ParseResult String
fromQName (HSE.UnQual _ name) = fromName name
fromQName qname = err qname

fromDecl :: (HSE.SrcInfo loc) => HSE.Decl loc -> ParseResult [Decl loc]
fromDecl (HSE.DataDecl _ (HSE.DataType _) Nothing dhead cons Nothing) =
    fromData dhead cons
fromDecl decl = do
    (name, term) <- fromBind decl
    return [VarDef name term]

fromBind :: (HSE.SrcInfo loc) => HSE.Decl loc -> ParseResult (Var, Term loc)
fromBind (HSE.PatBind _ (HSE.PVar _ name) (HSE.UnGuardedRhs _ exp) Nothing) =
    (,) <$> fromName name <*> fromExp exp
fromBind decl = err decl

fromData :: (HSE.SrcInfo loc) => HSE.DeclHead loc -> [HSE.QualConDecl loc] -> HSE.ParseResult [Decl loc]
fromData dhead cons = do
    (tcon, tvNames) <- splitDataHead dhead
    let tvs = tvNames `zip` [0..]
        ty = UTerm $ TApp tcon $ map (UVar . snd) tvs
        toDConTy = foldr (\t u -> UTerm $ TFun t u) ty
    forM cons $ \con -> do
        (dcon, argTys) <- fromCon (Map.fromList tvs) con
        return $ DataDef dcon $ toDConTy argTys

splitDataHead :: (HSE.SrcInfo loc) => HSE.DeclHead loc -> ParseResult (TCon, [String])
splitDataHead dhead = case dhead of
    HSE.DHead _ dcon -> do
        dcon <- fromName dcon
        return (dcon, [])
    HSE.DHParen _ dhead -> splitDataHead dhead
    HSE.DHApp _ dhead (HSE.UnkindedVar _ tvName) -> do
        (dcon, tvs) <- splitDataHead dhead
        tv <- fromName tvName
        return (dcon, tvs ++ [tv])
    dhead -> err dhead

fromCon :: (HSE.SrcInfo loc) => Map String TVar -> HSE.QualConDecl loc -> ParseResult (DCon, [PolyTy])
fromCon tvs (HSE.QualConDecl _ Nothing Nothing (HSE.ConDecl _ dcon tys)) = do
    dcon <- fromName dcon
    tys <- mapM (fromTy []) tys
    return (dcon, tys)
  where
    fromTy tyArgs (HSE.TyVar _ tvName) = do
        tvName <- fromName tvName
        UVar <$> tv tvName
    fromTy tyArgs (HSE.TyCon _ qname) = do
        tcon <- fromQName qname
        return $ UTerm $ TApp tcon tyArgs
    fromTy tyArgs (HSE.TyApp _ t u) = do
        u <- fromTy [] u
        fromTy (u:tyArgs) t
    fromTy [] (HSE.TyFun _ t u) = UTerm <$> (TFun <$> fromTy [] t <*> fromTy [] u)
    fromTy tyArgs (HSE.TyParen _ ty) = fromTy tyArgs ty
    fromTy _ ty = err ty

    tv a = maybe (fail "Unsupported: existential type variables") return $
           Map.lookup a tvs
fromCon tvs qcd = err qcd

fromExp :: (HSE.SrcInfo loc) => HSE.Exp loc -> ParseResult (Term loc)
fromExp (HSE.Var loc qname) =
    Tagged loc <$> (Var <$> fromQName qname)
fromExp (HSE.Con loc qname) =
    Tagged loc <$> (Con <$> fromQName qname)
fromExp (HSE.Lambda loc [HSE.PVar _ var] body) =
    Tagged loc <$> (Lam <$> fromName var <*> fromExp body)
fromExp (HSE.App loc f e) =
    Tagged loc <$> (App <$> fromExp f <*> fromExp e)
fromExp (HSE.Let loc binds body) =
    Tagged loc <$> (Let <$> fromBinds binds <*> fromExp body)
fromExp (HSE.Case loc exp alts) =
    Tagged loc <$> (Case <$> fromExp exp <*> mapM fromAlt alts)
fromExp (HSE.Paren _ exp) = fromExp exp
fromExp exp = err exp

fromBinds :: (HSE.SrcInfo loc) => HSE.Binds loc -> ParseResult [(Var, Term loc)]
fromBinds (HSE.BDecls _ decls) = mapM fromBind decls
fromBinds b = err b

fromAlt :: (HSE.SrcInfo loc) => HSE.Alt loc -> ParseResult (Pat loc, Term loc)
fromAlt (HSE.Alt _ pat (HSE.UnGuardedRhs _ exp) Nothing) =
    (,) <$> fromPat pat <*> fromExp exp
fromAlt alt = err alt

fromPat :: (HSE.SrcInfo loc) => HSE.Pat loc -> ParseResult (Pat loc)
fromPat (HSE.PVar loc var) = Tagged loc <$> (PVar <$> fromName var)
fromPat (HSE.PWildCard loc) = return $ Tagged loc PWild
fromPat (HSE.PApp loc qname pats) = Tagged loc <$> (PCon <$> fromQName qname <*> mapM fromPat pats)
fromPat (HSE.PParen _ pat) = fromPat pat
fromPat pat = err pat
