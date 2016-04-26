{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Unification
import Control.Unification.STVar
import Control.Unification.Types

import Data.Foldable
import Data.Traversable
import Data.Functor.Fixedpoint
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Control.Monad.RWS
import Control.Monad.Trans.Identity

data TyF dcon r
    = TCon dcon
    | TApp r r
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq dcon) => Unifiable (TyF dcon) where
    zipMatch (TCon dc1) (TCon dc2) = do
        guard $ dc1 == dc2
        return $ TCon dc1
    zipMatch (t1 `TApp` t2) (t1' `TApp` t2') = do
        return $ Right (t1, t1') `TApp` Right (t2, t2')
    zipMatch _ _ = mzero

type Ty0 = TyF String

type Ty = Fix Ty0
type MVar s = STVar s Ty0
type MTy s = UTerm Ty0 (MVar s)

type Err s = UFailure Ty0 (MVar s)

newtype M s a = M{ unM :: ExceptT (Err s) (RWST () () Integer (STBinding s)) a }
              deriving (Functor, Applicative, Monad)

instance BindingMonad Ty0 (MVar s) (M s) where
    lookupVar = M . lift . lift . lookupVar
    freeVar = M . lift . lift $ freeVar
    newVar = M . lift . lift . newVar
    bindVar v = M . lift . lift . bindVar v

instance MonadError (Err s) (M s) where
    throwError = M . throwError
    catchError (M act) = M . catchError act . (unM .)

foo :: forall s. M s (Maybe Ty)
foo = do
    let tInt = UTerm $ TCon "Int"
        tMaybe = UTerm $ TCon "Maybe"
    tv <- UVar <$> freeVar
    let t1 = UTerm $ tMaybe `TApp` tInt
        t2 = UTerm $ tMaybe `TApp` tv
    runIdentityT $ t1 =:= t2
    t2 <- runIdentityT $ applyBindings t2
    return $ freeze t2

runM :: (forall s. M s a) -> Either String a
runM act = runSTBinding $ do
    (x, _, _) <- runRWST (runExceptT $ unM act) () 0
    return $ bimap show id x
