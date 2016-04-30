{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Language.HM.Syntax where

import Language.HM.Remap

import Control.Unification

import Data.Foldable
import Data.Traversable
import Data.Functor.Fixedpoint
import Control.Monad.Writer
import Data.Set (Set)
import qualified Data.Set as Set

data TyF tcon a
    = TApp a a
    | TCon tcon
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq tcon) => Unifiable (TyF tcon) where
    zipMatch (TCon dc1) (TCon dc2) = do
        guard $ dc1 == dc2
        return $ TCon dc1
    zipMatch (t1 `TApp` t2) (t1' `TApp` t2') = do
        return $ Right (t1, t1') `TApp` Right (t2, t2')
    zipMatch _ _ = mzero

type TCon = String
type Ty0 = TyF TCon

type Ty = Fix Ty0

type TVar = Int
type PolyTy = UTerm Ty0 TVar

tApps :: UTerm (TyF tcon) v -> (UTerm (TyF tcon) v, [UTerm (TyF tcon) v])
tApps t = case go t of
    (t, ts) -> (t, reverse ts)
  where
    go (UTerm (TApp t u)) = case go t of (t, ts) -> (t, u:ts)
    go t = (t, [])

tFunArgs :: UTerm Ty0 v -> ([UTerm Ty0 v], UTerm Ty0 v)
tFunArgs = go
  where
    go (UTerm (TApp (UTerm (TApp (UTerm (TCon "Fun")) t)) u)) =
        case go u of (ts, t0) -> (t:ts, t0)
    go t = ([], t)

data Term0 dcon var
    = Var var
    | Con dcon
    | Lam var (Term0 dcon var)
    | App (Term0 dcon var) (Term0 dcon var)
    | Case (Term0 dcon var) [(Pat0 dcon var, Term0 dcon var)]
    | Let [(var, Term0 dcon var)] (Term0 dcon var)
    deriving Show

infixl 7 `App`

data Pat0 dcon var
    = PVar var
    | PWild
    | PCon dcon [Pat0 dcon var]
    deriving Show

type Var = String
type DCon = String

type Term = Term0 DCon Var
type Pat = Pat0 DCon Var

freeVarsOfTerm :: Term -> Set Var
freeVarsOfTerm = execWriter . go
  where
    go (Var v) = tell $ Set.singleton v
    go (Lam v e) = censor (Set.delete v) $ go e
    go Con{} = return ()
    go (App f e) = go f >> go e
    go (Case e as) = go e >> traverse_ alt as
    go (Let bs e) = do
        let bounds = Set.fromList $ map fst bs
        censor (Set.\\ bounds) $ do
            traverse_ (go . snd) bs
            go e

    alt (p, e) = censor (Set.\\ freeVarsOfPat p) $ go e

freeVarsOfPat :: Pat -> Set Var
freeVarsOfPat = execWriter . go
  where
    go PWild = return ()
    go (PVar v) = tell $ Set.singleton v
    go (PCon _ ps) = traverse_ go ps
