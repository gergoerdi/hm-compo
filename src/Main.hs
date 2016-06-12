import Language.HM.Syntax
import Language.HM.Pretty
import qualified Language.HM.Linear as Linear
import Language.HM.Compositional (Typing0((:-)))
import qualified Language.HM.Compositional as Compo
import Language.HM.Meta (freezePoly, generalize, zonk, MTy)
import Language.HM.Parser
import Text.Parsec.Pos

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

main :: IO ()
main = do
    let loc = initialPos sourceName
    s <- readFile sourceName
    decls <- case runP sourceName decl s of
        Left err -> error $ show err
        Right decls -> return $ decls
    let (dataDefs, varDefs) = partitionEithers $ map toEither decls
        dataDefs' = Map.fromList dataDefs
        toEither (DataDef dcon ty) = Left (dcon, ty)
        toEither (VarDef var term) = Right (var, term)

    -- let result = prettyTops $ runLinear loc dataDefs' varDefs
    -- print result
    -- putStrLn ""
    let result = prettyTops $ runCompo loc dataDefs' varDefs
    print result
  where
    sourceName = "demo/demo2.hm"

prettyTops :: Either Doc [(Var, PolyTy)] -> Doc
prettyTops (Left err) = err
prettyTops (Right vars) = vcat [ text name <+> dcolon <+> pPrint t
                               | (name, t) <- vars
                               ]

runLinear :: (Pretty loc)
          => loc
          -> Map DCon PolyTy
          -> [(Var, Term loc)]
          -> Either Doc [(Var, PolyTy)]
runLinear loc dataCons bindings = runST $ Linear.runM loc dataCons $ do
    polyVars <- Linear.tyCheckBinds bindings $ asks Linear.polyVars
    return $ map freeze . Map.toList $ polyVars
  where
    freeze (name, mty) = (name, fromMaybe (error err) $ freezePoly mty)
      where
        err = unwords [ "Ugh! Type variables escaped in type of"
                      , show name, "as", show mty
                      ]

runCompo :: (Pretty loc)
         => loc
         -> Map DCon PolyTy
         -> [(Var, Term loc)]
         -> Either Doc [(Var, PolyTy)]
runCompo loc dataCons bindings = runST $ Compo.runM loc dataCons $ do
    Compo.tyCheckBinds bindings $ \mc -> do
        pvars <- asks Compo.polyVars
        let monos = [ (name, t) | (name, mc :- t) <- Map.toList pvars ]
        tys <- traverse (traverse zonk) monos
        return $ map freeze tys
  where
    freeze :: (Var, MTy s) -> (Var, PolyTy)
    freeze (name, mty) = (name, fromMaybe (error err) $ freezePoly mty')
      where
        mty' = evalState (generalize fresh (const True) mty) 0
          where
            fresh = get <* modify succ

        err = unwords [ "Ugh! Type variables escaped in type of"
                      , show name, "as", show mty
                      ]
