{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas -Wno-name-shadowing #-}

-- | Port of free-foil-NBE's *eager-values* NbE into the lambda-n-ways harness,
-- specialised to the untyped lambda calculus.
--
-- This mirrors the representation shipped in @src/FreeFoil/NbE.hs@ of
-- free-foil-NBE: a semantic 'Value' whose term subterms are already values
-- ('VVar' / 'VApp') and whose scoped subterm (a lambda body) is a
-- 'ScopedClosure' capturing its own environment. @eval@ suspends lambda bodies
-- and reduces applications; @quote@ reads a value back, visiting each subterm
-- exactly once.
--
-- In the untyped fragment there is no @Pi@, so this coincides behaviourally
-- with the closure NbE in "Foil.NBE"; the point is to exercise *our*
-- (@Value@/@ScopedClosure@) representation inside the shared harness. The foil
-- primitives (scopes, names, substitutions) are reused from "Foil.NBE".
module Foil.EagerNBE (Tm, Value, impl) where

import Control.DeepSeq
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Foil.NBE
  ( Scope, Name (UnsafeName), NameBinder, Substitution, Distinct
  , Sinkable (sinkabilityProof), HasVar (makeVar)
  , emptyScope, extendScope, withFresh, withRefreshed, nameOf
  , lookupSubst, addSubst, addRename, identitySubst, sink )
import qualified Foil.NBE as F
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl

-- | Raw untyped terms — the syntax we evaluate from and quote back to.
data Tm n where
  TVar :: {-# UNPACK #-} !(Name n) -> Tm n
  TApp :: Tm n -> Tm n -> Tm n
  TLam :: {-# UNPACK #-} !(NameBinder n l) -> Tm l -> Tm n

instance NFData (Tm n) where
  rnf (TVar n) = rnf n
  rnf (TApp f x) = rnf f `seq` rnf x
  rnf (TLam b body) = rnf b `seq` rnf body

-- | Semantic values (eager-values representation). Term subterms are already
-- values; the lambda body is suspended as a 'ScopedClosure'. A stuck
-- application ('VApp' with a neutral head) needs no separate constructor.
data Value n where
  VVar :: {-# UNPACK #-} !(Name n) -> Value n
  VApp :: Value n -> Value n -> Value n
  VLam :: ScopedClosure n -> Value n

-- | A suspended lambda body together with its captured environment.
data ScopedClosure n where
  ScopedClosure ::
    Substitution Value n o -> {-# UNPACK #-} !(NameBinder n l) -> Tm l -> ScopedClosure o

instance HasVar Value where
  makeVar = VVar

instance Sinkable Value where
  sinkabilityProof rename = \case
    VVar x -> VVar (rename x)
    VApp f x -> VApp (sinkabilityProof rename f) (sinkabilityProof rename x)
    VLam (ScopedClosure env b body) ->
      VLam (ScopedClosure (sinkabilityProof rename env) b body)

-- | Evaluate a term into a value under an environment. Lambda bodies are
-- suspended; applications are reduced (beta) or left as a neutral 'VApp'.
eval :: Substitution Value i o -> Tm i -> Value o
eval env = \case
  TVar x -> lookupSubst env x
  TApp f x ->
    case eval env f of
      VLam (ScopedClosure env' binder body) ->
        eval (addSubst env' binder (eval env x)) body
      f' -> VApp f' (eval env x)
  TLam binder body -> VLam (ScopedClosure env binder body)

-- | Read a value back into a term. Each subterm is visited exactly once; the
-- suspended lambda body is evaluated under its own captured environment,
-- extended with a fresh neutral for the (refreshed) binder.
quote :: Distinct n => Scope n -> Value n -> Tm n
quote scope = \case
  VVar x -> TVar x
  VApp f x -> TApp (quote scope f) (quote scope x)
  VLam (ScopedClosure env binder body) ->
    withRefreshed scope (nameOf binder) $ \binder' ->
      let scope' = extendScope binder' scope
          env' = addRename (sink env) binder (nameOf binder')
       in TLam binder' (quote scope' (eval env' body))

normalise :: Tm F.VoidS -> Tm F.VoidS
normalise = quote emptyScope . eval identitySubst

-- Conversions to/from the harness' named representation. ----------------------

fromLC :: LC.LC IdInt.IdInt -> Tm F.VoidS
fromLC = go emptyScope IntMap.empty
  where
    go :: Distinct n => Scope n -> IntMap (Name n) -> LC.LC IdInt.IdInt -> Tm n
    go _ env (LC.Var (IdInt.IdInt x)) =
      case IntMap.lookup x env of
        Just name -> TVar name
        Nothing -> error ("unbound variable: " ++ show x)
    go scope env (LC.App f a) = TApp (go scope env f) (go scope env a)
    go scope env (LC.Lam (IdInt.IdInt x) body) =
      withFresh scope $ \binder ->
        let scope' = extendScope binder scope
            env' = IntMap.insert x (nameOf binder) (sink <$> env)
         in TLam binder (go scope' env' body)

toLC :: Tm n -> LC.LC IdInt.IdInt
toLC = \case
  TVar (UnsafeName i) -> LC.Var (IdInt.IdInt i)
  TApp f a -> LC.App (toLC f) (toLC a)
  TLam binder body ->
    let UnsafeName i = nameOf binder in LC.Lam (IdInt.IdInt i) (toLC body)

-- | Alpha-equivalence: reuse "Foil.NBE"'s tested comparison by viewing our raw
-- 'Tm' as its 'F.Expr' (same untyped syntax, same name/binder representation).
toExpr :: Tm n -> F.Expr n
toExpr = \case
  TVar x -> F.VarE x
  TApp f a -> F.AppE (toExpr f) (toExpr a)
  TLam b body -> F.LamE b (toExpr body)

aeq :: Tm n -> Tm n -> Bool
aeq a b = F.aeq_impl (toExpr a) (toExpr b)

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "NBE.FreeFoilEager",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = normalise,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = aeq
    }
