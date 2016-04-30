{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, StandaloneDeriving #-}

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

data TermF dcon var a
    = Var var
    | Con dcon
    | Lam var a
    | App a a
    | Case a [(PatFam a, a)]
    | Let [(var, a)] a
deriving instance (Show dcon, Show var, Show a, Show (PatFam a)) => Show (TermF dcon var a)

infixl 7 `App`

data PatF dcon var a
    = PVar var
    | PWild
    | PCon dcon [a]
    deriving Show

type family PatFam a
type instance PatFam (Fix (TermF dcon dvar)) = Fix (PatF dcon dvar)

type Var = String
type DCon = String

type Term0 = TermF DCon Var
type Pat0 = PatF DCon Var

type Term = Fix Term0
type Pat = Fix Pat0

freeVarsOfTerm :: Term -> Set Var
freeVarsOfTerm = execWriter . go
  where
    go e = case unFix e of
        Var v -> tell $ Set.singleton v
        Lam v e -> censor (Set.delete v) $ go e
        Con{} -> return ()
        App f e -> go f >> go e
        Case e as -> go e >> traverse_ alt as
        Let bs e -> censor (Set.\\ bound) $ traverse_ go (e:defs)
          where
            (vars, defs) = unzip bs
            bound = Set.fromList vars

    alt (p, e) = censor (Set.\\ freeVarsOfPat p) $ go e

freeVarsOfPat :: Pat -> Set Var
freeVarsOfPat = execWriter . go
  where
    go p = case unFix p of
        PWild -> return ()
        PVar v -> tell $ Set.singleton v
        PCon _ ps -> traverse_ go ps
