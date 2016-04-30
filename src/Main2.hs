{-# LANGUAGE Rank2Types #-}

import Language.HM.Syntax
import Language.HM.Pretty
import Language.HM.Compositional
import Language.HM.Meta ((~>), freezePoly)

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

dcolon :: Doc
dcolon = text "::"

foo :: M s Doc
-- foo = do
--     pvars <- foo'
--     return $ vcat [ text name <+> dcolon <+> pPrint t
--                   | (name, t) <- Map.toList pvars
--                   ]

-- foo' :: M s (Map Var PolyTy)
-- foo' = do
--     tyCheckBinds bs $ do
--         pvars <- asks polyVars
--         return $ fromMaybe (error "metavar escaped to top level!") $
--           -- traverse freezePoly pvars
--           traverse (maybe (pure $ UVar 0) $ \(_ :- t) -> fmap _ $ freeze t) pvars
foo = do
    (mc :- t) <- tyInfer e
    t <- runIdentityT $ applyBindings t
    return $ pPrint t
  where
    lam v = Fix . Lam v
    case' e = Fix . Case e
    var = Fix . Var
    pcon c = Fix . PCon c
    pvar = Fix . PVar
    con = Fix . Con
    app f e = Fix $ App f e
    infixl 7 `app`

    e = lam "f" $ lam "x" $ (var "f" `app` (var "f" `app` var "x"))

    bs = [ ("map", lam "f" $ lam "xs" $ case' (var "xs")
                   [ (pcon "Nil" [], con "Nil")
                   , (pcon "Cons" [pvar "x", pvar "xs"],
                      con "Cons" `app` (var "f" `app` var "x") `app`
                      (var "map" `app` var "f" `app` var "xs"))
                   ])
         , ("foldr", lam "f" $ lam "y" $ lam "xs" $ case' (var "xs")
                     [ (pcon "Nil" [], var "y")
                     , (pcon "Cons" [pvar "x", pvar "xs"],
                        var "f" `app` var "x" `app` (var "foldr" `app` var "f" `app` var "y" `app` var "xs"))
                     ])
         ]

runMain :: (forall s. M s a) -> a
runMain act = runSTBinding $ runM dataCons act
  where
    dataCons = Map.fromList [ ("Nil", tList alpha)
                            , ("Cons", alpha ~> tList alpha ~> tList alpha)
                            , ("MkPair", alpha ~> beta ~> tPair alpha beta)
                            ]

    alpha = UVar 0
    beta = UVar 1
    tList = UTerm . TApp (UTerm $ TCon "List")
    tPair t u = UTerm $ TApp (UTerm $ TApp (UTerm $ TCon "Pair") t) u
