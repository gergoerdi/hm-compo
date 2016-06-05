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
import Data.Graph

data TyF tcon a
    = TFun a a
    | TApp tcon [a]
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq tcon) => Unifiable (TyF tcon) where
    zipMatch (TFun t u) (TFun t' u') = return $ TFun (Right (t, t')) (Right (u, u'))
    zipMatch (TApp tc1 ts) (TApp tc2 us) = do
        guard $ tc1 == tc2
        guard $ length ts == length us
        return $ TApp tc1 $ map Right $ zip ts us
    zipMatch _ _ = mzero

type TCon = String
type Ty0 = TyF TCon

type Ty = Fix Ty0

type TVar = Int
type PolyTy = UTerm Ty0 TVar

(~>) :: UTerm (TyF tcon) v -> UTerm (TyF tcon) v -> UTerm (TyF tcon) v
t ~> u = UTerm $ TFun t u

infixr 7 ~>

tFunArgs :: UTerm (TyF tcon) v -> ([UTerm (TyF tcon) v], UTerm (TyF tcon) v)
tFunArgs = go
  where
    go (UTerm (TFun t u)) = case go u of (ts, t0) -> (t:ts, t0)
    go t = ([], t)

data Tagged a tag = Tagged{ getTag :: tag, unTag :: a } deriving (Show, Functor)

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

partitionBinds :: [(Var, Term loc)] -> [[(Var, Term loc)]]
partitionBinds binds = map flattenSCC . stronglyConnComp $ g
  where
    g = [((v, e), v, Set.toList (freeVarsOfTerm e)) | (v, e) <- binds]
