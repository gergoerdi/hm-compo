module Language.HM.Parser where

import Language.HM.Syntax
import Control.Unification
import Data.Functor.Fixedpoint

import Text.Parsec hiding (space)
import Text.Parsec.Layout

import Control.Monad (void)
import Data.Char
import Data.List (sort, nub)
import qualified Data.Map as Map

type Parser = Parsec String LayoutEnv

data Decl tag = DataDef DCon PolyTy
              | VarDef Var (Term tag)
              deriving Show

decl :: Parser [Decl ()]
decl = fmap concat . many $
       choice [ mapM ppDataDef =<< dataDef
              , (:[]) . uncurry VarDef <$> binding
              ]
  where
    ppDataDef (dcon, tvs, ty) = do
        let tvids = Map.fromList $ tvs `zip` [0..]
            tv a = maybe (fail "Unsupported: existential type variables") return $
                   Map.lookup a tvids
            walk (UTerm (TApp tcon ts)) = UTerm <$> TApp tcon <$> traverse walk ts
            walk (UVar a) = UVar <$> tv a
        ty' <- walk ty
        return $ DataDef dcon ty'

conName :: Parser String
conName = (<?> "constructor name") $
          spaced $ (:) <$> upper <*> many alphaNum

varName :: Parser String
varName = (<?> "variable name") $ try $ do
    s <- spaced $ (:) <$> lower <*> many alphaNum
    if s `elem` ["let", "in", "case", "of"]
      then unexpected $ unwords ["reserved word", show s]
      else return s

tag :: Parser a -> Parser (Tagged a ())
tag p = Tagged () <$> p

kw :: String -> Parser ()
kw = void . spaced . string

parens :: Parser a -> Parser a
parens = between (spaced lparen) (spaced rparen)
  where
    lparen = char '('
    rparen = char ')'

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

term :: Parser (Term ())
term = chainl1 atom (return (\x y -> Tagged () $ App x y))
  where
    atom = choice [ parens term
                  , tag $ letBlock
                  , tag $ caseBlock
                  , tag $ Var <$> varName
                  , tag $ Con <$> conName
                  , tag $ Lam <$> (kw "\\" *> varName <* kw "->") <*> term
                  ]

    letBlock = Let <$> iblock_ (kw "let") binding <*> (kw "in" *> term)

    caseBlock = iblock Case (kw "case" *> term <* kw "of") alt

    alt = (,) <$> (pat <* kw "->") <*> term

binding :: Parser (Var, Term ())
binding = (,) <$> (varName <* kw "=") <*> term

pat :: Parser (Pat ())
pat = (<?> "pattern") $
      choice [ parens pat
             , tag $ PVar <$> varName
             , tag $ kw "_" *> pure PWild
             , tag $ PCon <$> conName <*> many pat
             ]

iblock_ :: Parser x -> Parser a -> Parser [a]
iblock_ = iblock (const id)

iblock :: (a -> [b] -> c) -> Parser a -> Parser b -> Parser c
iblock f header body = do
    x <- header
    ys <- laidout body
    return $ f x ys

trim = reverse . dropWhile (== '\n') . reverse

s1 = unlines [ "data List a"
             , "  = Nil"
             , "  | Cons a (List a)"
             ]

s2 = unlines [ "map = \\f -> \\xs -> case xs of"
             , " Nil -> Nil"
             , " Cons x xs -> Cons (f x) (map f xs)"
             ]

s2' = unlines [ "map = \\f -> case xs of"
              , "  Nil -> Nil"
              ]

s4 = unlines [ "\\f -> \\x -> case xs of"
             , " Nil -> Nil"
             ]

s3 = unlines [ "map = f g"
             , " x"
             , "foo = q"
             ]

run :: Parser a -> String -> Either ParseError a
run p = runParser p defaultLayoutEnv "" . trim
