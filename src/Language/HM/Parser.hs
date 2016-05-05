module Language.HM.Parser where

import Language.HM.Syntax
import Control.Unification
import Data.Functor.Fixedpoint

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Indent
import Text.Parsec.Expr
import Control.Monad.Identity
import Data.List (sort, nub)

type Parser a = IndentParser String () a

conName :: Parser String
conName = lexeme $ (:) <$> upper <*> many alphaNum

varName :: Parser String
varName = try $ do
    s <- lexeme $ (:) <$> lower <*> many alphaNum
    if s `elem` ["let", "in", "case", "of"]
      then unexpected $ unwords ["reserved word", show s]
      else return s

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

tag :: Parser a -> Parser (Tagged a ())
tag p = Tagged () <$> p

kw :: String -> Parser ()
kw = void . lexeme . string

tyPart :: Parser (UTerm Ty0 String)
tyPart = choice [ parens ty
                , UVar <$> varName
                , UTerm <$> (TApp <$> conName <*> pure [])
                ]

tyFun :: UTerm Ty0 a -> UTerm Ty0 a -> UTerm Ty0 a
tyFun t u = UTerm $ TApp "Fun" [t, u]

ty :: Parser (UTerm Ty0 String)
ty = foldr1 tyFun <$> tyPart' `sepBy1` kw "->"
  where
    tyPart' = choice [ parens ty
                     , UVar <$> varName
                     , UTerm <$> (TApp <$> conName <*> many tyPart)
                     ]

dataDef :: Parser [(DCon, [String], UTerm Ty0 String)]
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

-- dataDef :: Parser (String, [String])
-- dataDef = kw "data" *> ((,) <$> conName <* kw "=" <*> conName `sepBy` kw "|")

term :: Parser (Term ())
term = buildExpressionParser table (sameOrIndented *> atom) <?> "term"
  where
    table = [[Infix (sameOrIndented >> spaces >> return (\x y -> Tagged () $ App x y)) AssocLeft]]

    atom :: Parser (Term ())
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

    alt = (,) <$> (pat <* kw "->") <*> withPos term

parens :: Parser a -> Parser a
parens p = kw "(" *> p <* kw ")"

pat :: Parser (Pat ())
pat = choice [ parens pat
             , tag $ PVar <$> varName
             , tag $ kw "_" *> pure PWild
             , tag $ PCon <$> conName <*> many pat
             ]

iblock_ :: Parser x -> Parser a -> Parser [a]
iblock_ = iblock (const id)

iblock :: (a -> [b] -> c) -> Parser a -> Parser b -> Parser c
iblock f header body = withPos $ do
    x <- withPos header
    ys <- many $ indented >> try body
    return $ f x ys

foo :: Parser a -> String -> Either ParseError a
foo p s = runIndent "" $ runPT p () "" s

-- s = unlines [ "let map = \\f -> \\xs -> case xs of Nil -> Nil in map"
--             ]
-- s = unlines [ "case xs of Nil -> Nil"
--             ]
s = unlines [ "\\f -> \\xs -> case xs of"
            , "              Nil -> Nil"
            , "              Cons x xs -> Cons (f x) (map f xs)"
            ]
