{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE RankNTypes   #-}
-- | A hand-written NbE for lambda-pi with a monomorphic value type: one
-- constructor per value form, so every value is a single heap object. It
-- runs the same algorithm as the generic normaliser on the same syntax and
-- serves as a baseline for the cost of the generic value domain. Evaluation
-- is call-by-need, a binder node captures its environment and keeps its body
-- as syntax, and readback evaluates each body once, so nested @Pi@ types
-- read back in linear time.
module LambdaPi.Monomorphic
  ( Val (..)
  , eval
  , quote
  , nfMono
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil

import LambdaPi.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | Values in scope @n@, weak-head normal at every position as in
-- 'FreeFoil.NbE.Value': the head of a 'VApp' is never a 'VLam'. 'eval' is
-- the only producer of values and maintains this in its application case.
data Val n where
  -- | A neutral variable.
  VVar :: {-# UNPACK #-} !(Name n) -> Val n
  -- | A stuck application: neutral head, suspended argument.
  VApp :: !(Val n) -> Val n -> Val n
  -- | A lambda closure: captured environment, binder and body.
  VLam ::
    !(Substitution Val i n) ->
    {-# UNPACK #-} !(NameBinder i l) ->
    FFTerm l ->
    Val n
  -- | A dependent function type: the domain as a value, the codomain as a
  -- closure.
  VPi ::
    Val n ->
    !(Substitution Val i n) ->
    {-# UNPACK #-} !(NameBinder i l) ->
    FFTerm l ->
    Val n

instance InjectName Val where
  injectName = VVar

-- | Evidence for sinking a captured environment into an extended scope;
-- 'sink' itself is a coercion.
instance Sinkable Val where
  sinkabilityProof rename = \case
    VVar x -> VVar (rename x)
    VApp f a -> VApp (sinkabilityProof rename f) (sinkabilityProof rename a)
    VLam env b body -> VLam (sinkabilityProof rename env) b body
    VPi dom env b body ->
      VPi (sinkabilityProof rename dom) (sinkabilityProof rename env) b body

-- | Evaluate a term under an environment; variables outside its domain
-- become neutrals.
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

-- | Read back a closure body under its binder: refresh the binder, map it to
-- the fresh name in the captured environment, evaluate the body once, quote.
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
