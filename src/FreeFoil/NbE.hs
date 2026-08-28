{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}

-- | Generic normalisation by evaluation (NbE) via free-foil.
module FreeFoil.NbE
  ( module Foil
  , module FreeFoil
  , Value (..)
  , quoteSuspendedScoped
  , freezeSuspendedScoped
  , vacuous
  , ensureVacuous
  , ensureVacuous1
  , Eval (..)
  , evalNode
  , eval
  , quote
  , quoteWhnf
  , nfNbe
  , whnfNbe
  , substitutionDomain
  ) where

import Control.Monad.Foil as Foil
import Control.Monad.Foil.Internal
  (
    Substitution (UnsafeSubstitution),
  )
import Control.Monad.Free.Foil as FreeFoil

import Data.Bifoldable
import Data.Void (Void, absurd)
import Unsafe.Coerce (unsafeCoerce)
import Data.Bifunctor
import Data.Monoid (Any (..))

import qualified Data.IntMap as IntMap

-- | The raw name identifiers a substitution currently maps (its domain).
-- Handy for inspecting the captured environment of a 'VSuspended' without
-- reaching into foil internals.
substitutionDomain :: Substitution e i o -> [Int]
substitutionDomain (UnsafeSubstitution m) = IntMap.keys m

-- | A semantic value for NbE, in the /eager-values/ representation.
--
-- 'VVar' is a neutral variable (a stuck computation whose head is a free
-- variable). 'VNode' is an evaluated syntax node with /no/ scoped subterms:
-- its term subterms are themselves values (already in the ambient scope @n@),
-- and its scoped positions are 'Void', so the type itself rules them out.
-- 'VSuspended' is a node /with/ scoped subterms, suspended as a whole: term
-- subterms are values, scoped subterms stay raw syntax, and one captured
-- environment serves them all. For example, a @Pi@ value keeps its domain as
-- an eager 'Value' while its codomain waits, un-evaluated, for the node's
-- environment. Every value thus has exactly one representation.
--
-- Because term subterms are already values, every subterm is evaluated and
-- quoted exactly once. This is what keeps 'quote' linear in the term size —
-- in particular, nested 'Pi' types do not re-normalise their codomains.
--
-- The type does not rule out redexes: nothing prevents one from building
-- @VNode (AppSig (VSuspended …) v)@, a beta-redex sitting in the semantic
-- domain. We rely on an invariant instead.
--
-- /Invariant./ Every value produced by 'eval' is weak-head normal at every
-- position: no node is an eliminator applied to the introduction form it
-- eliminates. Equivalently, each node is either an introduction form, or a
-- stuck eliminator whose principal argument is 'VVar'-headed.
--
-- The invariant is established by the object language's @eval@, which is the
-- only place that knows which constructors of @sig@ are eliminators: it matches
-- on them and reduces (see the @AppSig@ case in "LambdaPi"). Everything in this
-- module preserves it — 'quote', 'quoteSuspendedScoped' and 'evalNode' only
-- rebuild nodes and never apply an introduction form to an argument.
--
-- We do not enforce the invariant with types because the library is generic in
-- @sig@ and so cannot tell introductions from eliminators. A neutral\/normal
-- split would require the object language to supply that classification (two
-- signature bifunctors, or a class marking the eliminator constructors), which
-- we postpone deliberately: the present shape lets a language be plugged in
-- with a single @eval@ and no further boilerplate.
data Value binder sig n where
  VVar ::
    {-# UNPACK #-} !(Name n) -> Value binder sig n
  VNode ::
    sig Void (Value binder sig n) ->
    Value binder sig n
  -- | This fuses the node box with the closure: a lambda value is a
  -- 'VSuspended' around its sig cell, one heap object fewer than a node box
  -- around a per-position closure.
  VSuspended ::
    (Distinct i) =>
    Substitution (Value binder sig) i n ->
    sig (ScopedAST binder sig i) (Value binder sig n) ->
    Value binder sig n

instance Foil.InjectName (Value pat sig) where
  injectName = VVar

instance (Bifunctor sig) => Foil.Sinkable (Value pat sig) where
  sinkabilityProof :: (Name n -> Name l) -> Value pat sig n -> Value pat sig l
  sinkabilityProof rename (VVar n) =
    VVar (rename n)
  sinkabilityProof rename (VNode node) =
    VNode (bimap id (Foil.sinkabilityProof rename) node)
  sinkabilityProof rename (VSuspended env node) =
    VSuspended (Foil.sinkabilityProof rename env) (bimap id (Foil.sinkabilityProof rename) node)

-- | The default evaluation of a node with /no/ elimination rule: suspend every
-- scoped subterm under the current environment @env@ and evaluate every term
-- subterm with @ev env@. The evaluator is taken as @env -> AST -> Value@ (rather
-- than a pre-applied @AST -> Value@) so that a single @env@ both suspends the
-- node and drives the term subterms — they cannot accidentally
-- be evaluated under two different environments. An object language's @eval@ is
-- exactly its elimination rules (which inspect the principal value and reduce)
-- plus this one default for every introduction form — so a new language only
-- writes its redex cases. Preserves the 'Value' invariant: it never applies an
-- introduction form to an argument.
evalNode ::
  (Bifunctor sig, Bifoldable sig, Foldable (sig (ScopedAST binder sig i)), Distinct i) =>
  (Substitution (Value binder sig) i o -> AST binder sig i -> Value binder sig o) ->
  Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
evalNode ev env node =
  case ensureVacuous1 node of
    -- No scoped subterms: a plain node, and no environment to keep alive.
    Just node' -> VNode (bimap absurd (ev env) node')
    Nothing -> VSuspended env $ case ensureVacuous node of
      -- No term subterms either (e.g. a lambda): nothing to evaluate, so the
      -- cell is reused as it stands instead of being rebuilt.
      Just node' -> vacuous node'
      Nothing    -> bimap id (ev env) node

-- | Reuse a container that provably holds nothing at its parameter positions
-- at any other parameter type. Base's 'Data.Void.vacuous' is @fmap absurd@
-- and rebuilds the container; this one is a coercion. It is sound because a
-- value of @f 'Void'@ has no occupied parameter positions and the parameter
-- of a signature bifunctor is representational.
vacuous :: f Void -> f a
vacuous = unsafeCoerce

-- | Witness that a container holds nothing at its parameter positions. The
-- 'Just' result is the same heap object, not a rebuilt one — that is the
-- point: combined with 'vacuous' it lets a node be reused at another type
-- instead of being rebuilt field by field. The emptiness test constant-folds
-- per constructor in specialised code.
ensureVacuous :: Foldable f => f a -> Maybe (f Void)
ensureVacuous x
  | null x = Just (unsafeCoerce x)
  | otherwise = Nothing

-- | Witness that a node holds nothing at its /scoped/ (first) positions —
-- exactly what the 'Void' slots of 'VNode' require. As 'ensureVacuous', the
-- 'Just' result is the same heap object.
ensureVacuous1 :: Bifoldable f => f a b -> Maybe (f Void b)
ensureVacuous1 x
  | getAny (bifoldMap (const (Any True)) (const (Any False)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

-- | Evaluation as a library: an object language becomes an NbE instance by
-- giving its /elimination rules/. Everything else — variable lookup, suspending
-- scoped subterms, recursion, and quoting — is generic (see 'eval', 'quote').
--
-- 'evalSig' receives the /raw/ syntax node together with the current
-- environment. An /introduction/ form has no elimination rule and falls
-- through to the default, 'evalNode', which suspends a node with scoped
-- subterms whole and evaluates term subterms. A language overrides 'evalSig'
-- only to add its eliminators: evaluate the principal subterm and either
-- reduce (beta\/delta), or, when it is stuck on a neutral, rebuild the node.
-- Receiving the raw node (rather than an interpreted one) lets an eliminator
-- avoid allocating an intermediate interpreted cell that a redex would discard
-- immediately. Preserving the 'Value' invariant is the instance's
-- responsibility.
class (Bifunctor sig, Bifoldable sig, forall scopedTerm. Foldable (sig scopedTerm)) => Eval binder sig where
  evalSig ::
    (Distinct o, Distinct i) =>
    Scope o ->
    Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig scope env = evalNode (eval scope) env

-- | Generic evaluation into the semantic domain. Looks up variables and hands
-- a node, still raw, to the language's 'evalSig' together with the current
-- environment.
eval ::
  (Eval binder sig, Distinct o, Distinct i) =>
  Scope o ->
  Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval scope !env = \case
  Var x -> lookupSubst env x
  Node node -> evalSig scope env node

-- | Quote a value back into an AST. Each subterm is processed exactly once:
-- term subterms recurse directly, scoped subterms are read back under their
-- binder via 'quoteSuspendedScoped' (which re-evaluates them via 'eval').
quote ::
  (Eval binder sig, Foil.Distinct n, Foil.HasNameBinders binder, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote scope = \case
  VVar x -> Var x
  VNode node ->
    Node $!
      bimap
        absurd
        (quote scope)
        node
  VSuspended env node ->
    Node $!
      bimap
        (quoteSuspendedScoped scope env)
        (quote scope)
        node

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the captured environment to map it to a fresh neutral, evaluate the
-- body once under that environment, and quote the result.
quoteSuspendedScoped ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.Distinct i,
    Foil.CoSinkable binder,
    Foil.HasNameBinders binder
  ) =>
  Foil.Scope n ->
  Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
{-# INLINABLE quoteSuspendedScoped #-}
quoteSuspendedScoped scope env (ScopedAST bind body) =
  Foil.withRefreshedPattern scope bind $ \extendEnv bind' scope' ->
    case Foil.assertDistinct bind of
      Foil.Distinct ->
        ScopedAST bind' (quote scope' (eval scope' (extendEnv env) body))

-- | Normal form by NbE: evaluate into the semantic domain, then quote fully.
-- Generic over any 'Eval' instance — an object language gets @nfNbe@ for free.
nfNbe ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.HasNameBinders binder,
    Foil.CoSinkable binder
  ) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nfNbe #-}
nfNbe scope = quote scope . eval scope identitySubst

-- | Weak-head normal form by NbE: evaluate into the semantic domain, then read
-- back only the head. Shares 'eval' with 'nfNbe' and differs solely in how far
-- quoting is driven — 'quoteWhnf' does /not/ go under binders.
--
-- One eager-values caveat. Because 'eval' evaluates term positions eagerly, the
-- arguments of a stuck neutral are already normalised here, unlike a lazy whnf
-- that would leave them untouched. The weak-head/full distinction therefore
-- shows up only at /scoped/ positions: 'whnfNbe' leaves a redex under a binder
-- alone (e.g. @whnfNbe (\\x. (\\y. y) x) = \\x. (\\y. y) x@), whereas 'nfNbe'
-- reduces it. Both agree on head reduction and on neutral spines.
whnfNbe ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.HasNameBinders binder,
    Foil.CoSinkable binder,
    Foil.SinkableK binder
  ) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
whnfNbe scope = quoteWhnf scope . eval scope identitySubst

-- | Shallow readback producing a weak-head normal form: expose the head node,
-- fully quote its term subterms (they are already normal — eager values), but
-- /freeze/ its scoped subterms rather than normalising under their binders (see
-- 'freezeSuspendedScoped').
quoteWhnf ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.HasNameBinders binder,
    Foil.CoSinkable binder,
    Foil.SinkableK binder
  ) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf scope = \case
  VVar x -> Var x
  VNode node ->
    Node $
      bimap
        absurd
        (quote scope)
        node
  VSuspended env node ->
    Node $
      bimap
        (freezeSuspendedScoped scope env)
        (quote scope)
        node

-- | Freeze one scoped subterm of a suspended node /without/ evaluating under
-- its binder: refresh the binder and substitute the captured environment —
-- quoted to terms by 'quoteSubst' — into the still-syntactic body. Unlike
-- 'quoteSuspendedScoped', no beta\/delta reduction happens under the binder
-- ('substitute' only renames), so a redex there survives. This is what makes
-- 'whnfNbe' weak-head rather than full normalisation.
freezeSuspendedScoped ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.Distinct i,
    Foil.CoSinkable binder,
    Foil.HasNameBinders binder,
    Foil.SinkableK binder
  ) =>
  Foil.Scope n ->
  Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeSuspendedScoped scope env (ScopedAST bind body) =
  Foil.withRefreshedPattern scope bind $ \extendSubst bind' scope' ->
    let subst = extendSubst (quoteSubst scope env)
     in ScopedAST bind' (substitute scope' subst body)

-- | Quote every value in a substitution's codomain, turning a semantic
-- environment into a syntactic one. Used by 'freezeSuspendedScoped' to substitute
-- a closure's captured environment back into its body without normalising it.
quoteSubst ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.HasNameBinders binder,
    Foil.CoSinkable binder
  ) =>
  Foil.Scope n ->
  Substitution (Value binder sig) i n ->
  Substitution (AST binder sig) i n
quoteSubst scope (UnsafeSubstitution m) =
  UnsafeSubstitution (IntMap.map (quote scope) m)
