{-# LANGUAGE Rank2Types #-}

import Language.HM.Syntax
import Language.HM.Pretty
import Language.HM.Compositional
import Language.HM.Meta ((~>), freezePoly)
import Language.HM.Parser

import Control.Unification
import Control.Unification.STVar (runSTBinding)

import Control.Monad.Trans.Identity

import Data.Functor.Fixedpoint
import Control.Monad.RWS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass
import Data.Either (partitionEithers)

main :: IO ()
main = do
    s <- readFile "demo1.hm"
    decls <- case runP decl s of
        Left err -> error $ show err
        Right decls -> return decls
    let (dataDefs, varDefs) = partitionEithers $ map toEither decls
        dataDefs' = Map.fromList dataDefs
        toEither (DataDef dcon ty) = Left (dcon, ty)
        toEither (VarDef var term) = Right (var, term)

    let result = run dataDefs' varDefs
    print result

run :: Map DCon PolyTy -> [(Var, Term tag)] -> Doc
run dataCons bindings = runSTBinding $ runM dataCons $ do
    tyCheckBinds bindings $ \mc -> do
        pvars <- asks polyVars
        let monos = [ (name, t) | (name, Just (mc :- t)) <- Map.toList pvars ]
        tys <- zip (map fst monos) <$> (runIdentityT $ applyBindingsAll . map snd $ monos)
        return $ vcat [ text name <+> dcolon <+> pPrint t
                      | (name, t) <- tys
                      ]


dcolon :: Doc
dcolon = text "::"
