module Language.HM.Parser where

import Language.HM.Syntax
import Control.Unification
import Data.Functor.Fixedpoint

import Text.Trifecta
import Text.Trifecta.Indentation

import Control.Monad (void)
import Data.Char
import Data.List (sort, nub)

type IP = IndentationParserT Token Parser

conName :: IP String
conName = token $ (:) <$> upper <*> many alphaNum

varName :: IP String
varName = try $ do
    s <- token $ (:) <$> lower <*> many alphaNum
    if s `elem` ["let", "in", "case", "of"]
      then unexpected $ unwords ["reserved word", show s]
      else return s

tag :: IP a -> IP (Tagged a ())
tag p = Tagged () <$> p

kw :: String -> IP ()
kw = void . symbol

tyPart :: IP (UTerm Ty0 String)
tyPart = choice [ parens ty
                , UVar <$> varName
                , UTerm <$> (TApp <$> conName <*> pure [])
                ]

tyFun :: UTerm Ty0 a -> UTerm Ty0 a -> UTerm Ty0 a
tyFun t u = UTerm $ TApp "Fun" [t, u]

ty :: IP (UTerm Ty0 String)
ty = foldr1 tyFun <$> tyPart' `sepBy1` kw "->"
  where
    tyPart' = choice [ parens ty
                     , UVar <$> varName
                     , UTerm <$> (TApp <$> conName <*> many tyPart)
                     ]

dataDef :: IP [(DCon, [String], UTerm Ty0 String)]
dataDef = do
    ((tname, params), dconSpecs) <- (,) <$> header <*> dcon `sepBy` kw "|"
    let t = UTerm $ TApp tname $ map UVar params
        toDConTy = foldr tyFun t
    return [(dcon, params, dconTy) | (dcon, ts) <- dconSpecs, let dconTy = toDConTy ts]
  where
    header = kw "data" *> ((,) <$> conName <*> many varName) <* kw "="
    dcon = (,) <$> conName <*> many tyPart

distinct :: (Ord a) => [a] -> Bool
distinct xs = let xs' = sort xs in nub xs' == xs'

term :: IP (Term ())
term = chainl1 (localIndentation Gt atom) (spaces >> return (\x y -> Tagged () $ App x y))
  where
    atom = choice [ parens term
                  , tag $ letBlock
                  , tag $ caseBlock
                  , tag $ Var <$> varName
                  , tag $ Con <$> conName
                  , tag $ Lam <$> (kw "\\" *> varName <* kw "->") <*> term
                  ]

    letBlock = Let <$> iblock_ (kw "let") binding <*> (kw "in" *> term)

    binding = (,) <$> (varName <* kw "=") <*> term

    caseBlock = iblock Case (kw "case" *> term <* kw "of") alt

    alt = (,) <$> (pat <* kw "->") <*> term

pat :: IP (Pat ())
pat = choice [ parens pat
             , tag $ PVar <$> varName
             , tag $ kw "_" *> pure PWild
             , tag $ PCon <$> conName <*> many pat
             ]

iblock_ :: IP x -> IP a -> IP [a]
iblock_ = iblock (const id)

iblock :: (a -> [b] -> c) -> IP a -> IP b -> IP c
iblock f header body = do
    x <- ignoreAbsoluteIndentation header
    ys <- absoluteIndentation $ many body
    return $ f x ys

s1 = unlines [ "data List a"
             , "    = Nil"
             , "    | Cons a (List a)"
             ]

s2 = unlines [ "\\f -> \\xs -> case xs of"
             , "  Nil -> Nil"
             , "  Cons x xs -> Cons (f x) (map f xs)"
             ]

foo :: IP a -> String -> Result a
foo p = parseString p' mempty
  where
    p' = evalIndentationParserT p $ mkIndentationState 1 infIndentation True Ge
