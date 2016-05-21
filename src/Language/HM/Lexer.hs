{-# LANGUAGE RecordWildCards, TupleSections #-}
module Language.HM.Lexer (tokenize, Token(..)) where

import Text.Regex.Applicative
import Text.Parsec.Pos
import Data.Char (isSpace, isAlpha, isAlphaNum, isPunctuation, isSymbol)
import Control.Monad
import Control.Applicative.Alternative
import Control.Monad.State

data RawToken = RawWord String
              | RawSymbol String
              | RawNewline
              | Space Int
              deriving Show

rawToken :: RE Char RawToken
rawToken = asum [ RawWord <$> word
                , RawNewline <$ sym '\n'
                , RawNewline <$ comment
                , RawSymbol <$> punct
                , RawSymbol <$> symbol
                , Space . length <$> some (sym ' ')
                ]
  where
    word :: RE Char String
    word = (:) <$> psym isAlpha <*> many (psym isAlphaNum <|> psym isSymbol)

    symbol :: RE Char String
    symbol = some $ psym isSymbol <|> psym isPunctuation

    punct :: RE Char String
    punct = (:[]) <$> psym (`elem` "()[]")

    comment :: RE Char ()
    comment = void $ string "--" *> optional restOfLine *> sym '\n'
      where
        restOfLine = psym isSpace *> many (psym (/= '\n'))

    optional re = (() <$ re) <|> pure ()

data Token = Word String
           | Symbol String
           | Newline Int
           deriving Show

data St = St{ pos :: SourcePos
            , start :: Bool
            , firstLine :: Bool
            }
        deriving Show

emptySt :: SourceName -> St
emptySt sourceName = St{ pos = initialPos sourceName, start = True, firstLine = True }

pp :: SourceName -> [RawToken] -> [(SourcePos, Token)]
pp sourceName rs = concat $ evalState (mapM go rs) $ emptySt sourceName
  where
    printable :: (String -> Token) -> String -> State St [(SourcePos, Token)]
    printable mkT s = do
        St{..} <- state $ \st -> (st, update st)
        let col = sourceColumn pos
            t = mkT s
        return $ map (pos,) $
          if start {- && not firstLine -} then [Newline col, t] else [t]
      where
        update St{..} = St{ pos = updatePosString pos s
                          , start = False
                          , firstLine = False
                          }

    go :: RawToken -> State St [(SourcePos, Token)]
    go (RawWord s) = printable Word s
    go (RawSymbol s) = printable Symbol s
    go RawNewline = do
        modify $ \st@St{..} -> st{ pos = updatePosChar pos '\n', start = True }
        return []
    go (Space n) = do
        modify $ \st@St{..} -> st{ pos = incSourceColumn pos n }
        return []

tokenize :: SourceName -> String -> Maybe [(SourcePos, Token)]
tokenize sourceName = fmap (pp sourceName) . match (many rawToken)

s :: String
s = unlines [ "foo"
            , "  bar baz"
            , " quux"
            ]
