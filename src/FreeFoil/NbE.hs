{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- | Normalisation by evaluation, generic in the signature of the object
-- language. A language is a signature bifunctor @sig@ and a binder type, as
-- in "Control.Monad.Free.Foil"; to normalise its terms it supplies one 'Eval'
-- instance, its elimination rules. The semantic domain ('Value'), evaluation
-- ('eval'), readback ('quote') and the normalisers 'nfNbe' and 'whnfNbe' are
-- generic.
--
-- The normaliser is untyped and intensional: it decides β and the language's
-- own reductions, not η, and it keeps one signature for terms and values, so
-- neutral and normal values are not told apart by type (see 'Value').
--
-- The recursive functions are @INLINABLE@, so a language can specialise them
-- to its signature; "LambdaPi" shows the @SPECIALIZE@ pragmas that remove
-- all dictionary passing from the loop.
module FreeFoil.NbE
  ( -- * Semantic domain
    Value (..)
    -- * Evaluation
  , Eval (..)
  , eval
  , evalNode
    -- * Readback
  , quote
  , quoteSuspendedScoped
  , nfNbe
  , quoteWhnf
  , freezeSuspendedScoped
  , whnfNbe
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Substitution (..))
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..), substitute)
import           Data.Bifoldable             (Bifoldable (..))
import           Data.Bifunctor              (Bifunctor (..))
import qualified Data.IntMap                 as IntMap
import           Data.Monoid                 (Any (..))
import           Data.Void                   (Void, absurd)
import           Unsafe.Coerce               (unsafeCoerce)

-- * Semantic domain

-- | A semantic value in scope @n@. Term subterms are values already; only
-- scoped subterms, the bodies under binders, are suspended. A 'VSuspended'
-- node keeps its term subterms as values, its scoped subterms as syntax, and
-- one captured environment for them all: a @Pi@ holds its domain as a value
-- while its codomain waits, unevaluated, for the environment. Since 'eval'
-- and 'quote' each visit every subterm exactly once, readback is linear in
-- the size of the term, and nested @Pi@ types do not re-normalise their
-- codomains.
--
-- /Invariant./ Every value 'eval' produces is weak-head normal at every
-- position: no node is an eliminator applied to the introduction form it
-- eliminates. The type cannot enforce this, as it does not know which
-- constructors of @sig@ eliminate; the language's 'evalSig' establishes it,
-- and every function here preserves it.
data Value binder sig n where
  -- | A neutral variable.
  VVar :: {-# UNPACK #-} !(Foil.Name n) -> Value binder sig n
  -- | A node without scoped subterms.
  VNode :: sig Void (Value binder sig n) -> Value binder sig n
  -- | A node with scoped subterms, suspended under its environment; the
  -- environment sits in the constructor, so the node costs one heap object
  -- beside its @sig@ cell.
  VSuspended ::
    Foil.Distinct i =>
    Foil.Substitution (Value binder sig) i n ->
    sig (ScopedAST binder sig i) (Value binder sig n) ->
    Value binder sig n

instance Foil.InjectName (Value binder sig) where
  injectName = VVar

instance Bifunctor sig => Foil.Sinkable (Value binder sig) where
  sinkabilityProof :: (Foil.Name n -> Foil.Name l) -> Value binder sig n -> Value binder sig l
  sinkabilityProof rename (VVar x) =
    VVar (rename x)
  sinkabilityProof rename (VNode node) =
    VNode (bimap id (Foil.sinkabilityProof rename) node)
  sinkabilityProof rename (VSuspended env node) =
    VSuspended (Foil.sinkabilityProof rename env) (bimap id (Foil.sinkabilityProof rename) node)

-- * Evaluation

-- | A language becomes an NbE instance by giving its elimination rules:
-- 'evalSig' receives a raw node and the environment, matches the
-- eliminators, evaluates the principal subterm and either reduces or, on a
-- neutral, rebuilds the node as a 'VNode'. Every other node falls through to
-- 'evalNode'. The node arrives raw so that a redex never builds the
-- interpreted node it would discard. The instance upholds the 'Value'
-- invariant; "LambdaPi" is a one-rule example.
class (Bifunctor sig, Bifoldable sig) => Eval binder sig where
  evalSig ::
    (Foil.Distinct o, Foil.Distinct i) =>
    Foil.Scope o ->
    Foil.Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig scope env = evalNode (eval scope) env

-- | Evaluate a term under an environment: look variables up, hand nodes to
-- 'evalSig'.
eval ::
  (Eval binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  Foil.Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval scope !env = \case
  Var x -> Foil.lookupSubst env x
  Node node -> evalSig scope env node

-- | Evaluate a node that has no elimination rule: suspend it whole under the
-- environment if it has scoped subterms, otherwise evaluate its term
-- subterms. The evaluator comes as @env -> term -> value@ so that one
-- environment both suspends the node and drives its subterms.
evalNode ::
  (Bifunctor sig, Bifoldable sig, Foil.Distinct i) =>
  (Foil.Substitution (Value binder sig) i o -> AST binder sig i -> Value binder sig o) ->
  Foil.Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
{-# INLINE evalNode #-}
evalNode ev env node =
  case ensureBivacuousFirst node of
    Just node' -> VNode (bimap absurd (ev env) node')
    Nothing -> VSuspended env $ case ensureBivacuousSecond node of
      -- Nothing to evaluate either (a lambda, say): reuse the cell as it is.
      Just node' -> vacuous node'
      Nothing    -> bimap id (ev env) node

-- A node whose parameter positions are provably empty is the same heap
-- object at any parameter type, so it is reused by coercion rather than
-- rebuilt field by field. The coercions are sound because a signature
-- bifunctor is representational in its parameters; the emptiness tests
-- constant-fold per constructor in specialised code.

vacuous :: f Void -> f a
vacuous = unsafeCoerce

ensureBivacuousFirst :: Bifoldable f => f a b -> Maybe (f Void b)
{-# INLINE ensureBivacuousFirst #-}
ensureBivacuousFirst x
  | getAny (bifoldMap (const (Any True)) (const (Any False)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

ensureBivacuousSecond :: Bifoldable f => f a b -> Maybe (f a Void)
{-# INLINE ensureBivacuousSecond #-}
ensureBivacuousSecond x
  | getAny (bifoldMap (const (Any False)) (const (Any True)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

-- * Readback

-- | Read a value back into a term. Term subterms recurse directly; scoped
-- subterms are read back under their binder by 'quoteSuspendedScoped'.
quote ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote scope = \case
  VVar x -> Var x
  VNode node -> Node $! bimap absurd (quote scope) node
  VSuspended env node -> Node $! bimap (quoteSuspendedScoped scope env) (quote scope) node

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the captured environment with it as a fresh neutral, evaluate the
-- body once under that environment, and quote the result.
quoteSuspendedScoped ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.HasNameBinders binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
{-# INLINABLE quoteSuspendedScoped #-}
quoteSuspendedScoped scope env (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct -> ScopedAST binder' (quote scope' (eval scope' (extendEnv env) body))

-- | Normal form: evaluate, then read back fully.
nfNbe ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nfNbe #-}
nfNbe scope = quote scope . eval scope Foil.identitySubst

-- | Read back the head of a value only: quote its term subterms, which are
-- values already, and freeze its scoped subterms instead of normalising under
-- their binders.
quoteWhnf ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf scope = \case
  VVar x -> Var x
  VNode node -> Node $ bimap absurd (quote scope) node
  VSuspended env node -> Node $ bimap (freezeSuspendedScoped scope env) (quote scope) node

-- | Freeze one scoped subterm of a suspended node without evaluating under
-- its binder: refresh the binder and substitute the captured environment,
-- quoted to terms, into the still-syntactic body. 'substitute' only renames,
-- so a redex under the binder survives.
freezeSuspendedScoped ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.HasNameBinders binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeSuspendedScoped scope env (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendSubst binder' scope' ->
    ScopedAST binder' (substitute scope' (extendSubst (quoteSubst scope env)) body)

-- | Quote every value in an environment, turning it into a syntactic
-- substitution.
quoteSubst ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  Foil.Substitution (AST binder sig) i n
quoteSubst scope (Foil.UnsafeSubstitution m) =
  Foil.UnsafeSubstitution (IntMap.map (quote scope) m)

-- | Weak-head normal form: evaluate, then read back the head only. Shares
-- 'eval' with 'nfNbe'; 'quoteWhnf' does not go under binders, so a redex
-- under a lambda survives. Term positions are values already, so the two
-- readbacks differ only at scoped positions.
whnfNbe ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
whnfNbe scope = quoteWhnf scope . eval scope Foil.identitySubst
