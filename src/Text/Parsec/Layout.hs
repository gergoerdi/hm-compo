{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

-- | These are Haskell-style layout combinators for parsec 3 by Edward Kmett,
-- first seen on StackOverflow <http://stackoverflow.com/a/3023615/33796>.
-- Should be fairly self-explanatory, with the following notes:
--
-- * You must use the provided `space` combinator to parse spaces.  This interacts poorly with
-- the "Text.Parsec.Token" modules, unfortunately.
--
-- * Uses \"\{\" and \"\}\" for explicit blocks.  This is hard-coded for the time being. 

module Text.Parsec.Layout
    ( laidout          
    , semi             
    , space            
    , spaced           
    , LayoutEnv        
    , defaultLayoutEnv 
    , HasLayoutEnv(..) 
    , maybeFollowedBy
    ) where

import Control.Applicative ((<$>))
import Control.Monad (guard)

import Data.Char (isSpace)

import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim hiding (State)
import Text.Parsec.Char hiding (space)
import Control.Lens (Simple, Lens, over, (^.))

data LayoutContext = NoLayout | Layout Int deriving (Eq,Ord,Show)

-- | Keeps track of necessary context for layout parsers.
data LayoutEnv = Env
    { envLayout :: [LayoutContext]
    , envBol :: Bool -- if true, must run offside calculation
    }

-- | For embedding layout information into a larger parse state.  Instantiate
-- this class if you need to use this together with other user state.
class HasLayoutEnv u where
    layoutEnv :: Simple Lens u LayoutEnv

instance HasLayoutEnv LayoutEnv where
    layoutEnv = id

-- | A fresh layout.
defaultLayoutEnv :: LayoutEnv
defaultLayoutEnv = Env [] True

pushContext :: (HasLayoutEnv u, Stream s m c) => LayoutContext -> ParsecT s u m ()
pushContext ctx = modifyEnv $ \env -> env { envLayout = ctx:envLayout env }

modifyEnv :: (HasLayoutEnv u, Monad m) => (LayoutEnv -> LayoutEnv) -> ParsecT s u m ()
modifyEnv = modifyState . over layoutEnv

getEnv :: (HasLayoutEnv u, Monad m) => ParsecT s u m LayoutEnv
getEnv = (^.layoutEnv) <$> getState

popContext :: (HasLayoutEnv u, Stream s m c) => String -> ParsecT s u m ()
popContext loc = do
    (_:xs) <- envLayout <$> getEnv
    modifyEnv $ \env' -> env' { envLayout = xs }
  <|> unexpected ("empty context for " ++ loc)

getIndentation :: (HasLayoutEnv u, Stream s m c) => ParsecT s u m Int
getIndentation = depth . envLayout <$> getEnv where
    depth :: [LayoutContext] -> Int
    depth (Layout n:_) = n
    depth _ = 0

pushCurrentContext :: (HasLayoutEnv u, Stream s m c) => ParsecT s u m ()
pushCurrentContext = do
    indent <- getIndentation
    col <- sourceColumn <$> getPosition
    pushContext . Layout $ max (indent+1) col

maybeFollowedBy :: Stream s m c => ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m a
t `maybeFollowedBy` x = do t' <- t; optional x; return t'

-- | @(\``maybeFollowedBy`\` space)@
spaced :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m a -> ParsecT s u m a
spaced t = t `maybeFollowedBy` space

data Layout = VSemi | VBrace | Other Char deriving (Eq,Ord,Show)

-- TODO: Parse C-style #line pragmas out here
layout :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m Layout
layout = try $ do
    bol <- envBol <$> getEnv
    whitespace False (cont bol)
  where
    cont :: (HasLayoutEnv u, Stream s m Char) => Bool -> Bool -> ParsecT s u m Layout
    cont True = offside
    cont False = onside

    -- TODO: Parse nestable {-# LINE ... #-} pragmas in here
    whitespace :: (HasLayoutEnv u, Stream s m Char) =>
        Bool -> (Bool -> ParsecT s u m Layout) -> ParsecT s u m Layout
    whitespace x k =
            try (string "{-" >> nested k >>= whitespace True)
        <|> try comment
        <|> do newline; whitespace True offside
        <|> do tab; whitespace True k
        <|> do (satisfy isSpace <?> "space"); whitespace True k
        <|> k x

    comment :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m Layout
    comment = do
        string "--"
        many (satisfy ('\n'/=))
        newline
        whitespace True offside

    nested :: (HasLayoutEnv u, Stream s m Char) =>
        (Bool -> ParsecT s u m Layout) ->
        ParsecT s u m (Bool -> ParsecT s u m Layout)
    nested k =
            try (do string "-}"; return k)
        <|> try (do string "{-"; k' <- nested k; nested k')
        <|> do newline; nested offside
        <|> do anyChar; nested k

    offside :: (HasLayoutEnv u, Stream s m Char) => Bool -> ParsecT s u m Layout
    offside x = do
        p <- getPosition
        pos <- compare (sourceColumn p) <$> getIndentation
        case pos of
            LT -> do
                popContext "the offside rule"
                modifyEnv $ \env -> env { envBol = True }
                return VBrace
            EQ -> return VSemi
            GT -> onside x

    -- we remained onside.
    -- If we skipped any comments, or moved to a new line and stayed onside, we return a single a ' ',
    -- otherwise we provide the next char
    onside :: (HasLayoutEnv u, Stream s m Char) => Bool -> ParsecT s u m Layout
    onside True = return $ Other ' '
    onside False = do
        modifyEnv $ \env -> env { envBol = False }
        Other <$> anyChar

layoutSatisfies :: (HasLayoutEnv u, Stream s m Char) => (Layout -> Bool) -> ParsecT s u m ()
layoutSatisfies p = guard . p =<< layout

virtual_lbrace :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m ()
virtual_lbrace = pushCurrentContext

virtual_rbrace :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m ()
virtual_rbrace = eof <|> try (layoutSatisfies (VBrace ==) <?> "outdent")

-- | Consumes one or more spaces, comments, and onside newlines in a layout rule.
space :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m String
space = do
    try $ layoutSatisfies (Other ' ' ==)
    return " "
  <?> "space"

-- | Recognize a semicolon including a virtual semicolon in layout.
semi :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m String
semi = do
    try $ layoutSatisfies p
    return ";"
  <?> "semi-colon"
  where
        p VSemi = True
        p (Other ';') = True
        p _ = False

lbrace :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m String
lbrace = do
    char '{'
    pushContext NoLayout
    return "{"

rbrace :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m String
rbrace = do
    char '}'
    popContext "a right brace"
    return "}"

-- | Repeat a parser in layout, separated by (virtual) semicolons.
laidout :: (HasLayoutEnv u, Stream s m Char) => ParsecT s u m a -> ParsecT s u m [a]
laidout p = try (braced statements) <|> vbraced statements where
    braced = between (spaced lbrace) (spaced rbrace)
    vbraced = between (spaced virtual_lbrace) (spaced virtual_rbrace)
    statements = p `sepBy` spaced semi
