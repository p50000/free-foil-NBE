{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

-- | A hand-written, monomorphic NbE for lambda-pi.
--
-- This is a baseline for measuring the generic normaliser of "FreeFoil.NbE",
-- not a part of the framework. It normalises the same syntax as
-- 'LambdaPi.nfNbe' (@AST FFPattern TermSig@) with the same algorithm, but its
-- values form a monomorphic data type with one constructor per value form,
-- so every value is a single heap object. The difference between the two
-- normalisers estimates what generated monomorphic code could gain while
-- keeping free-foil syntax as input and output.
--
-- As in the generic normaliser, evaluation is call-by-need, a binder node
-- captures the environment and keeps its body as syntax, and readback
-- refreshes each binder and evaluates the body once, so nested @Pi@ types are
-- read back in linear time.
module LambdaPi.Monomorphic
  ( Val (..)
  , eval
  , quote
  , nfMono
  ) where

import Control.Monad.Foil
  ( Distinct
  , InjectName (..)
  , Name
  , NameBinder
  , Scope
  , Sinkable (..)
  , Substitution
  , addRename
  , addSubst
  , extendScope
  , identitySubst
  , lookupSubst
  , nameOf
  , sink
  , withRefreshed
  )
import Control.Monad.Free.Foil (AST (..), ScopedAST (..))

import LambdaPi.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | Semantic values of lambda-pi in scope @n@.
--
-- The invariant is that of 'FreeFoil.NbE.Value': a value is weak-head normal
-- at every position, i.e. the head of a 'VApp' is never a 'VLam'. Here 'eval'
-- is the only producer of values, and its application case maintains this.
data Val n where
  -- | A neutral variable.
  VVar :: {-# UNPACK #-} !(Name n) -> Val n
  -- | A stuck application. The head is neutral; the argument is suspended.
  VApp :: !(Val n) -> Val n -> Val n
  -- | A lambda closure: the captured environment, the binder and the body.
  VLam ::
    !(Substitution Val i n) ->
    {-# UNPACK #-} !(NameBinder i l) ->
    FFTerm l ->
    Val n
  -- | A dependent function type: the domain as a value, then a closure for
  -- the codomain, as in 'VLam'.
  VPi ::
    Val n ->
    !(Substitution Val i n) ->
    {-# UNPACK #-} !(NameBinder i l) ->
    FFTerm l ->
    Val n

instance InjectName Val where
  injectName = VVar

-- | Needed to 'sink' a captured environment into an extended scope. In
-- practice 'sink' is a coercion, and this instance only serves as evidence.
instance Sinkable Val where
  sinkabilityProof rename = \case
    VVar x -> VVar (rename x)
    VApp f a -> VApp (sinkabilityProof rename f) (sinkabilityProof rename a)
    VLam env b body -> VLam (sinkabilityProof rename env) b body
    VPi dom env b body ->
      VPi (sinkabilityProof rename dom) (sinkabilityProof rename env) b body

-- | Evaluate a term under an environment that maps its free variables to
-- values. Variables outside the environment's domain become neutrals.
eval :: Substitution Val i o -> FFTerm i -> Val o
eval !env = \case
  Var x -> lookupSubst env x
  Node node -> case node of
    AppSig fun arg ->
      case eval env fun of
        VLam env' binder body -> eval (addSubst env' binder (eval env arg)) body
        fun' -> VApp fun' (eval env arg)
    LamSig (ScopedAST (FFPatternVar binder) body) -> VLam env binder body
    PiSig dom (ScopedAST (FFPatternVar binder) body) ->
      VPi (eval env dom) env binder body

-- | Read a value back into a term in normal form.
quote :: Distinct n => Scope n -> Val n -> FFTerm n
quote scope = \case
  VVar x -> Var x
  VApp fun arg -> Node (AppSig (quote scope fun) (quote scope arg))
  VLam env binder body ->
    Node (LamSig (quoteScoped scope env binder body))
  VPi dom env binder body ->
    Node (PiSig (quote scope dom) (quoteScoped scope env binder body))

-- | Read back the body of a closure under its binder: refresh the binder
-- against the ambient scope, map it to the fresh name in the captured
-- environment, evaluate the body once and quote the result.
quoteScoped ::
  Distinct n =>
  Scope n ->
  Substitution Val i n ->
  NameBinder i l ->
  FFTerm l ->
  ScopedAST FFPattern TermSig n
quoteScoped scope env binder body =
  withRefreshed scope (nameOf binder) $ \binder' ->
    let scope' = extendScope binder' scope
        env' = addRename (sink env) binder (nameOf binder')
     in ScopedAST (FFPatternVar binder') (quote scope' (eval env' body))

-- | Normal form by the monomorphic NbE.
nfMono :: Distinct n => Scope n -> FFTerm n -> FFTerm n
nfMono scope = quote scope . eval identitySubst
