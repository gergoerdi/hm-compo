{-# LANGUAGE RecordWildCards #-}
module Language.HM.Lexer (tokenize, Token(..)) where

import Text.Regex.Applicative
import Data.Char (isSpace, isAlpha, isAlphaNum, isPunctuation, isSymbol)
import Control.Monad
import Control.Monad.State

data RawToken = RawWord String
              | RawSymbol String
              | RawNewline
              | Space Int
              deriving Show

rawToken :: RE Char RawToken
rawToken = RawWord <$> word <|>
           RawSymbol <$> symbol <|>
           RawNewline <$ sym '\n' <|>
           Space . length <$> some (sym ' ')
  where
    word :: RE Char String
    word = (:) <$> psym isAlpha <*> many (psym isAlphaNum <|> psym isSymbol)

    symbol :: RE Char String
    symbol = some $ psym isPunctuation <|> psym isSymbol


data Token = Word String
           | Symbol String
           | Newline Int
           deriving Show

data St = St{ col :: Int
            , start :: Bool
            , firstLine :: Bool
            }
        deriving Show

emptySt :: St
emptySt = St{ col = 0, start = True, firstLine = True }

pp :: [RawToken] -> [Token]
pp rs = concat $ evalState (mapM go rs) emptySt
  where
    printable :: Token -> State St [Token]
    printable t = do
        St{..} <- state $ \st -> (st, st{ start = False, firstLine = False })
        return $ if start {- && not firstLine -} then [Newline col, t] else [t]

    go :: RawToken -> State St [Token]
    go (RawWord s) = printable $ Word s
    go (RawSymbol s) = printable $ Symbol s
    go RawNewline = do
        modify $ \st@St{..} -> st{ col = 0, start = True }
        return []
    go (Space n) = do
        modify $ \st@St{..} -> st{ col = col + n }
        return []

tokenize :: String -> Maybe [Token]
tokenize = fmap pp . match (many rawToken)

s :: String
s = unlines [ "foo"
            , "  bar baz"
            , " quux"
            ]
