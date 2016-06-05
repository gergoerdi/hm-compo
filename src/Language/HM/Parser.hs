{-# LANGUAGE RecordWildCards #-}
module Language.HM.Parser
       ( runP, vlist, SourceName
       , decl, term, Decl(..)
       ) where

import Language.HM.Lexer
import Language.HM.Syntax
import Control.Unification
import Data.Functor.Fixedpoint

import Text.Parsec.Prim hiding (runP)
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.Combinator

import Control.Monad (void, guard)
import Data.Char
import Data.List (sort, nub)
import qualified Data.Map as Map

data St = St{ colStack :: [Int] }

startSt :: St
startSt = St{ colStack = [0] } -- XX

type Parser = Parsec [(SourcePos, Token)] St

token' :: (Token -> Maybe a) -> Parser a
token' = tokenPrim (showTok . snd) nextPos . (. snd)
  where
    showTok (Word s) = show s
    showTok (Symbol s) = show s
    showTok (Newline _) = "newline"

    nextPos pos (pos', t) _ts = pos'

satisfy :: (String -> Bool) -> Parser String
satisfy p = word (\s -> guard (p s) >> return s)

word :: (String -> Maybe a) -> Parser a
word p = token' $ \t -> case t of
    Word s -> p s
    _ -> Nothing

newline :: Parser Int
newline = token' $ \t -> case t of
    Newline col -> return col
    _ -> Nothing

reserved :: String -> Parser ()
reserved s = (<?> unwords ["keyword", "'" ++ s ++ "'"]) $ void $ satisfy (== s)

symbol :: String -> Parser ()
symbol s = (<?> unwords ["symbol", "'" ++ s ++ "'"]) $
           token' $ \t -> case t of
               Symbol s' | s' == s -> Just ()
               _ -> Nothing

conName :: Parser String
conName = (<?> "constructor name") $ try $
          satisfy $ \(c:_) -> isUpper c

varName :: Parser String
varName = (<?> "variable name") $ try $ do
    s <- satisfy $ \(c:_) -> isLower c
    if s `elem` ["data", "let", "in", "case", "of"]
      then unexpected $ unwords ["reserved word", show s]
      else return s

parens :: Parser a -> Parser a
parens = between lparen rparen
  where
    lparen = symbol "("
    rparen = symbol ")"

data Decl tag = DataDef DCon PolyTy
              | VarDef Var (Term tag)
              deriving Show

decl :: Parser [Decl SourcePos]
decl = fmap concat . vlist $
       choice [ mapM ppDataDef =<< dataDef
              , (:[]) . uncurry VarDef <$> binding
              ]
  where
    ppDataDef (dcon, tvs, ty) = do
        let tvids = Map.fromList $ tvs `zip` [0..]
            tv a = maybe (fail "Unsupported: existential type variables") return $
                   Map.lookup a tvids
        ty' <- traverse tv ty
        return $ DataDef dcon ty'

tyPart :: Parser (UTerm Ty0 String)
tyPart = choice [ parens ty
                , UVar <$> varName
                , UTerm <$> (TApp <$> conName <*> pure [])
                ]

ty :: Parser (UTerm Ty0 String)
ty = foldr1 (\t u -> UTerm $ TFun t u) <$> tyPart' `sepBy1` symbol "->"
  where
    tyPart' = choice [ parens ty
                     , UVar <$> varName
                     , UTerm <$> (TApp <$> conName <*> many tyPart)
                     ]

dataDef :: Parser [(DCon, [String], UTerm Ty0 String)]
dataDef = do
    ((tname, params), dconSpecs) <- (,) <$> header <*> dcon `sepBy` symbol "|"
    let t = UTerm $ TApp tname $ map UVar params
        toDConTy = foldr (\t u -> UTerm $ TFun t u) t
    return [(dcon, params, dconTy) | (dcon, ts) <- dconSpecs, let dconTy = toDConTy ts]
  where
    header = reserved "data" *> ((,) <$> conName <*> many varName) <* symbol "="
    dcon = (,) <$> conName <*> many tyPart

distinct :: (Ord a) => [a] -> Bool
distinct xs = let xs' = sort xs in nub xs' == xs'

vlist :: Parser a -> Parser [a]
vlist p = do
    col <- newline
    modifyState $ \st@St{..} -> st{ colStack = col:colStack }
    let cont = try $ do
            i <- newline
            guard $ i == col
    p `sepBy` cont

multiline1 :: Parser a -> Parser [a]
multiline1 p = do
    St{ colStack = col:_ } <- getState
    let cont = try $ do
            i <- newline
            guard $ i > col
    concat <$> many1 p `sepBy1` cont

term :: Parser (Term SourcePos)
term = foldl1 app <$> multiline1 atom
  where
    app :: Term SourcePos -> Term SourcePos -> Term SourcePos
    app f@(Tagged loc1 _) e@(Tagged loc2 _) = Tagged loc1 (App f e)

    atom = choice [ parens term
                  , tag $ letBlock
                  , tag $ caseBlock
                  , tag $ Var <$> varName
                  , tag $ Con <$> conName
                  , tag $ Lam <$> (symbol "\\" *> varName <* symbol "->") <*> term
                  ]

    letBlock = Let <$> iblock_ (reserved "let") binding <*> (reserved "in" *> term)

    caseBlock = iblock Case (reserved "case" *> term <* reserved "of") alt

    alt = (,) <$> (pat <* symbol "->") <*> term

binding :: Parser (Var, Term SourcePos)
binding = (,) <$> (varName <* symbol "=") <*> term

pat :: Parser (Pat SourcePos)
pat = (<?> "pattern") $
      choice [ parens pat
             , tag $ PVar <$> varName
             , tag $ symbol "_" *> pure PWild
             , tag $ PCon <$> conName <*> many pat
             ]

iblock_ :: Parser x -> Parser a -> Parser [a]
iblock_ = iblock (const id)

iblock :: (a -> [b] -> c) -> Parser a -> Parser b -> Parser c
iblock f header body = do
    St{ colStack = col:_ } <- getState
    x <- header
    let startInline = do
            y <- body
            ys <- option [] startNewline
            return $ y:ys
        startNewline = do
            i <- try $ do
                i <- newline
                guard $ i > col
                return i
            modifyState $ \st@St{..} -> st{ colStack = i:colStack }
            let cont = try $ do
                    i' <- newline
                    guard $ i' == i
            ys <- body `sepBy` cont
            modifyState $ \st@St{..} -> st{ colStack = tail colStack }
            return ys
    ys <- startNewline <|> startInline
    return $ f x ys

tag :: Parser a -> Parser (Tagged a SourcePos)
tag p = do
    pos <- getPosition
    x <- p
    return $ Tagged pos x

runP :: SourceName -> Parser a -> String -> Either ParseError a
runP sourceName p s = case tokenize sourceName s of
    Nothing -> Left $ newErrorMessage (Message "Tokenization failed") $ initialPos ""
    Just ts -> runParser p startSt "" ts
