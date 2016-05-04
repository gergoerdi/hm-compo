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

data Tagged a tag = Tagged{ getTag :: tag, unTag :: a } deriving Show

data TermF dcon var tag
    = Var var
    | Con dcon
    | Lam var (Term0 dcon var tag)
    | App (Term0 dcon var tag) (Term0 dcon var tag)
    | Case (Term0 dcon var tag) [(Pat0 dcon var tag, Term0 dcon var tag)]
    | Let [(var, Term0 dcon var tag)] (Term0 dcon var tag)
    deriving Show

type Term0 dcon var tag = Tagged (TermF dcon var tag) tag

infixl 7 `App`

data PatF dcon var tag
    = PVar var
    | PWild
    | PCon dcon [Pat0 dcon var tag]
    deriving Show

type Pat0 dcon var tag = Tagged (PatF dcon var tag) tag

type Var = String
type DCon = String

type Term a = Term0 DCon Var a
type Pat a = Pat0 DCon Var a

freeVarsOfTerm :: Term a -> Set Var
freeVarsOfTerm = execWriter . go
  where
    go e = case unTag e of
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

freeVarsOfPat :: Pat a -> Set Var
freeVarsOfPat = execWriter . go
  where
    go p = case unTag p of
        PWild -> return ()
        PVar v -> tell $ Set.singleton v
        PCon _ ps -> traverse_ go ps
