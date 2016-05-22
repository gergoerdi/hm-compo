import Language.HM.Syntax
import Language.HM.Pretty
import qualified Language.HM.Linear as Linear
-- import Language.HM.Compositional (Typing0((:-)))
-- import qualified Language.HM.Compositional as Compo
import Language.HM.Meta (freezePoly, generalize, zonk, zonkPoly)
import Language.HM.Parser

import Control.Unification
import Control.Monad.ST

import Control.Monad.Trans.Identity
import Control.Monad.State

import Data.Functor.Fixedpoint
import Control.Monad.RWS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass
import Data.Either (partitionEithers)

{-
main :: IO ()
main = do
    s <- readFile "demo5.hm"
    es <- case runP "demo5.hm" (vlist term) s of
        Left err -> error $ show err
        Right terms -> return terms
    let result = runST $ Linear.runM mempty $ do
            ts <- mapM Linear.tyInfer es
            ts <- mapM zonk ts
            return $ map pPrint ts

    print result
-}

main :: IO ()
main = do
    s <- readFile "demo2.hm"
    decls <- case runP "demo2.hm" decl s of
        Left err -> error $ show err
        Right decls -> return $ decls
    let (dataDefs, varDefs) = partitionEithers $ map toEither decls
        dataDefs' = Map.fromList dataDefs
        toEither (DataDef dcon ty) = Left (dcon, ty)
        toEither (VarDef var term) = Right (var, term)

    -- let result = prettyTops $ runCompo dataDefs' varDefs
    -- print result

    let result = prettyTops $ runLinear dataDefs' varDefs
    print result

prettyTops :: Either Doc [(Var, PolyTy)] -> Doc
prettyTops (Left err) = err
prettyTops (Right vars) = vcat [ text name <+> dcolon <+> pPrint t
                               | (name, t) <- vars
                               ]

runLinear :: (Pretty tag)
          => Map DCon PolyTy
          -> [(Var, Term tag)]
          -> Either Doc [(Var, PolyTy)]
runLinear dataCons bindings = runST $ Linear.runM dataCons $ do
    polyVars <- Linear.tyCheckBinds bindings $ asks Linear.polyVars
    polyVars <- traverse zonkPoly polyVars
    -- runIdentityT $ forM (Map.toList polyVars) $ \(name, mty) -> do
    --     mty <- applyBindings mty
    --     return $ freeze (name, mty)
    return $ map freeze . Map.toList $ polyVars
  where
    freeze (name, mty) = (name, fromMaybe (error err) $ freezePoly mty)
      where
        err = unwords [ "Ugh! Type variables escaped in type of"
                      , show name, "as", show mty
                      ]
{-
runCompo :: Map DCon PolyTy -> [(Var, Term tag)] -> Either Doc [(Var, PolyTy)]
runCompo dataCons bindings = runSTBinding $ Compo.runM dataCons $ do
    Compo.tyCheckBinds bindings $ \mc -> do
        pvars <- asks Compo.polyVars
        let monos = [ (name, t) | (name, Just (mc :- t)) <- Map.toList pvars ]
        tys <- runIdentityT $ zip (map fst monos) <$> (applyBindingsAll . map snd $ monos)
        return $ map freeze tys
  where
    freeze (name, mty) = (name, fromMaybe (error err) $ freezePoly mty')
      where
        mty' = evalState (generalize fresh (const True) mty) 0
          where
            fresh = get <* modify succ

        err = unwords [ "Ugh! Type variables escaped in type of"
                      , show name, "as", show mty
                      ]
-}

dcolon :: Doc
dcolon = text "::"
