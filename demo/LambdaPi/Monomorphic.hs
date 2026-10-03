{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

-- | A hand-written, monomorphic NbE for lambda-pi.
--
-- This is a baseline for measuring the generic normaliser of "FreeFoil.NbE",
-- not a part of the framework. It normalises the same scope-safe syntax as
-- 'LambdaPi.nfNbe' (free-foil's generated @AST FFPattern TermSig@), with the
-- same evaluation strategy and the same foil name handling, but its semantic
-- domain is a monomorphic data type with one constructor per value form.
--
-- Thus every value is a single heap object: a lambda value is one 'VLam'
-- carrying its environment, an unpacked binder and the body, and a stuck
-- application is one 'VApp'. The generic domain cannot do this, since it can
-- only speak about a node through the signature bifunctor, so a generic value
-- is a constructor box around a @sig@ cell. The gap between the two
-- normalisers therefore bounds what a generated (rather than hand-written)
-- monomorphic value type could gain while keeping free-foil syntax as input
-- and output.
--
-- The algorithm mirrors the generic one step by step:
--
-- * evaluation is call-by-need: an argument is suspended as a thunk, both in
--   a beta-reduction and in a stuck application;
-- * a binder node (@Lam@, @Pi@) captures the current environment and keeps
--   its scoped body as raw syntax, while the domain of a @Pi@ is a (lazy)
--   value;
-- * readback refreshes each binder against the ambient scope, maps it to a
--   fresh neutral in the captured environment, and evaluates the body once,
--   so nested @Pi@ types are read back in linear time.
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
