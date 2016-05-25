{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Language.HM.Monad where

import Language.HM.Syntax
import Language.HM.Remap
import Language.HM.Meta
import Language.HM.Error
import Language.HM.Pretty
import Text.Parsec.Pos

import Control.Monad.ST
import Data.STRef
import Control.Unification.Types

import Text.PrettyPrint.HughesPJClass hiding (first)

import Data.Foldable
import Data.Functor.Fixedpoint
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS hiding (Product)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Product)
import Control.Monad.Identity
import Control.Monad.Trans.Identity
import Control.Arrow (first, second)
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Graph
import Data.Maybe
import Data.Function

data R loc = R{ dataCons :: Map DCon PolyTy
              , loc :: (loc, Doc)
              }
type Located err loc = Tagged err (loc, Doc)

newtype TC ctx err s loc a = TC{ unTC :: ExceptT (Located err loc) (RWST (R loc, ctx) () Int (ST s)) a }
                           deriving ( Functor, Applicative, Monad
                                    , MonadState Int
                                    )

instance MonadReader ctx (TC ctx err s loc) where
    ask = TC $ asks snd
    local f = TC . local (second f) . unTC

instance MonadError err (TC ctx err s loc) where
    throwError err = do
        loc <- TC $ asks (loc . fst)
        TC . throwError $ Tagged loc err
    catchError act handler = TC $ catchError (unTC act) (unTC . handler . unTag)

instance MonadTC Ty0 (MVar s) (TC ctx err s loc) where
    freshVar = do
        id <- state $ \i -> (i, succ i)
        ref <- TC . lift . lift $ newSTRef Nothing
        return $ STVar id ref
    readVar (STVar _ ref) = TC . lift . lift $ readSTRef ref
    writeVar (STVar _ ref) t = TC . lift . lift $ writeSTRef ref $ Just t

class UErr err t v | err -> t v where
    uerr :: UTerm t v -> UTerm t v -> UFailure t v -> err

infix 4 =:=
(=:=) :: (UErr err Ty0 (MVar s)) => MTy s -> MTy s -> TC ctx err s loc (MTy s)
t =:= u = do
    res <- runExceptT $ unify t u
    case res of
        Left err -> do
            t <- zonk t
            u <- zonk u
            throwError $ uerr t u err
        Right () -> return t

askDataCon :: DCon -> TC ctx err s loc (Maybe PolyTy)
askDataCon dcon = TC $ asks $ Map.lookup dcon . dataCons . fst

withLoc :: (Pretty src) => Tagged src loc -> TC ctx err s loc a -> TC ctx err s loc a
withLoc (Tagged loc src) = TC . local (first $ \r -> r{ loc = (loc, pPrint src) }) . unTC

freshTVar :: TC ctx err s loc TVar
freshTVar = TC $ get <* modify succ

runTC :: (Pretty loc, Pretty err)
      => SourceName
      -> Map DCon PolyTy
      -> ctx
      -> TC ctx err s loc a
      -> ST s (Either Doc a)
runTC sourceName dataCons ctx act = do
    let pos = initialPos sourceName
        -- loc = (pos, empty)
    (x, _, _) <- runRWST (runExceptT $ unTC act) (R{..}, ctx) 0
    return $ either (Left . pPrintErr) Right $ x
  where
    pPrintErr (Tagged (loc, src) err) =
        vcat [ pPrint loc
             , nest 4 src
             , text ""
             , pPrint err
             ]
