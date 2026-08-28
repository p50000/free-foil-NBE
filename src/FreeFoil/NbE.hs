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
  , ScopedClosure (..)
  , Eval (..)
  , evalNode
  , eval
  , quote
  , quoteScopedClosure
  , quoteWhnf
  , freezeScopedClosure
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

import Data.Bifunctor

import qualified Data.IntMap as IntMap

-- | The raw name identifiers a substitution currently maps (its domain).
-- Handy for inspecting the captured environment of a 'ScopedClosure' without
-- reaching into foil internals.
substitutionDomain :: Substitution e i o -> [Int]
substitutionDomain (UnsafeSubstitution m) = IntMap.keys m

-- | A semantic value for NbE, in the /eager-values/ representation.
--
-- 'VVar' is a neutral variable (a stuck computation whose head is a free
-- variable). 'VNode' is an evaluated syntax node whose /term/ subterms are
-- themselves values (already in the ambient scope @n@) and whose /scoped/
-- subterms are 'ScopedClosure's — suspended bodies that each carry their own
-- captured environment. Storing the two positions differently is exactly what
-- a node with both needs: a @Pi@'s domain is a term position (an eager 'Value'
-- in the ambient scope) while its codomain is a scoped position (a
-- 'ScopedClosure' deferred under the binder), so the two no longer have to
-- share one environment.
--
-- Because term subterms are already values, every subterm is evaluated and
-- quoted exactly once. This is what keeps 'quote' linear in the term size —
-- in particular, nested 'Pi' types do not re-normalise their codomains.
--
-- The type does not rule out redexes: nothing prevents one from building
-- @VNode (AppSig (VNode (LamSig …)) v)@, a beta-redex sitting in the semantic
-- domain. We rely on an invariant instead.
--
-- /Invariant./ Every value produced by 'eval' is weak-head normal at every
-- position: no 'VNode' is an eliminator applied to the introduction form it
-- eliminates. Equivalently, each 'VNode' is either an introduction form, or a
-- stuck eliminator whose principal argument is 'VVar'-headed.
--
-- The invariant is established by the object language's @eval@, which is the
-- only place that knows which constructors of @sig@ are eliminators: it matches
-- on them and reduces (see the @AppSig@ case in "LambdaPi"). Everything in this
-- module preserves it — 'quote', 'quoteScopedClosure', 'sinkScopedClosure' and
-- 'evalNode' only rebuild nodes and never apply an introduction form to an
-- argument.
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
    sig (ScopedClosure binder sig n) (Value binder sig n) ->
    Value binder sig n

-- | A suspended scoped subterm: a body together with the environment captured
-- where it was introduced. Evaluation of the body is deferred until 'quote'
-- goes under the binder.
data ScopedClosure binder sig n where
  ScopedClosure ::
    (Distinct i) =>
    Substitution (Value binder sig) i n ->
    ScopedAST binder sig i ->
    ScopedClosure binder sig n

instance Foil.InjectName (Value pat sig) where
  injectName = VVar

instance (Bifunctor sig) => Foil.Sinkable (Value pat sig) where
  sinkabilityProof :: (Name n -> Name l) -> Value pat sig n -> Value pat sig l
  sinkabilityProof rename (VVar n) =
    VVar (rename n)
  sinkabilityProof rename (VNode node) =
    VNode (bimap (sinkScopedClosure rename) (Foil.sinkabilityProof rename) node)

-- | Sink a suspended scoped subterm: only the captured environment moves to
-- the wider scope; the (still un-evaluated) body is untouched.
sinkScopedClosure ::
  (Bifunctor sig) =>
  (Name n -> Name l) ->
  ScopedClosure pat sig n ->
  ScopedClosure pat sig l
sinkScopedClosure rename (ScopedClosure env body) =
  ScopedClosure (Foil.sinkabilityProof rename env) body

-- | The default evaluation of a node with /no/ elimination rule: suspend every
-- scoped subterm under the current environment @env@ and evaluate every term
-- subterm with @ev env@. The evaluator is taken as @env -> AST -> Value@ (rather
-- than a pre-applied @AST -> Value@) so that a single @env@ both captures into
-- each 'ScopedClosure' and drives the term subterms — they cannot accidentally
-- be evaluated under two different environments. An object language's @eval@ is
-- exactly its elimination rules (which inspect the principal value and reduce)
-- plus this one default for every introduction form — so a new language only
-- writes its redex cases. Preserves the 'Value' invariant: it never applies an
-- introduction form to an argument.
evalNode ::
  (Bifunctor sig, Distinct i) =>
  (Substitution (Value binder sig) i o -> AST binder sig i -> Value binder sig o) ->
  Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
evalNode ev env = VNode . bimap (ScopedClosure env) (ev env)

-- | Evaluation as a library: an object language becomes an NbE instance by
-- giving its /elimination rules/. Everything else — variable lookup, suspending
-- scoped subterms, recursion, and quoting — is generic (see 'eval', 'quote').
--
-- 'evalSig' receives the /raw/ syntax node together with the current
-- environment. An /introduction/ form has no elimination rule and falls
-- through to the default, 'evalNode', which suspends scoped subterms as
-- 'ScopedClosure's and evaluates term subterms. A language overrides 'evalSig'
-- only to add its eliminators: evaluate the principal subterm and either
-- reduce (beta\/delta), or, when it is stuck on a neutral, rebuild the node.
-- Receiving the raw node (rather than an interpreted one) lets an eliminator
-- avoid allocating an intermediate interpreted cell that a redex would discard
-- immediately. Preserving the 'Value' invariant is the instance's
-- responsibility.
class (Bifunctor sig) => Eval binder sig where
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
-- binder via 'quoteScopedClosure' (which re-evaluates them via 'eval').
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
        (quoteScopedClosure scope)
        (quote scope)
        node

-- | Read back a suspended scoped subterm: refresh the binder, extend the
-- captured environment to map it to a fresh neutral, evaluate the body once
-- under that environment, and quote the result.
quoteScopedClosure ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.CoSinkable binder,
    Foil.HasNameBinders binder
  ) =>
  Foil.Scope n ->
  ScopedClosure binder sig n ->
  ScopedAST binder sig n
{-# INLINABLE quoteScopedClosure #-}
quoteScopedClosure scope (ScopedClosure env (ScopedAST bind body)) =
  Foil.withRefreshedPattern scope bind $ \extendEnv bind' ->
    case Foil.assertDistinct bind' of
      Foil.Distinct ->
        case Foil.assertDistinct bind of
          Foil.Distinct ->
            let scope' = Foil.extendScopePattern bind' scope
                env' = extendEnv env
             in ScopedAST bind' (quote scope' (eval scope' env' body))

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
-- 'freezeScopedClosure').
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
        (freezeScopedClosure scope)
        (quote scope)
        node

-- | Read back a suspended scoped subterm /without/ evaluating under its binder:
-- refresh the binder and substitute the captured environment — quoted to terms
-- by 'quoteSubst' — into the still-syntactic body. Unlike 'quoteScopedClosure',
-- no beta\/delta reduction happens under the binder ('substitute' only renames),
-- so a redex there survives. This is what makes 'whnfNbe' weak-head rather than
-- full normalisation.
freezeScopedClosure ::
  ( Eval binder sig,
    Foil.Distinct n,
    Foil.HasNameBinders binder,
    Foil.CoSinkable binder,
    Foil.SinkableK binder
  ) =>
  Foil.Scope n ->
  ScopedClosure binder sig n ->
  ScopedAST binder sig n
freezeScopedClosure scope (ScopedClosure env (ScopedAST bind body)) =
  Foil.withRefreshedPattern scope bind $ \extendSubst bind' ->
    case Foil.assertDistinct bind' of
      Foil.Distinct ->
        let scope' = Foil.extendScopePattern bind' scope
            subst = extendSubst (quoteSubst scope env)
         in ScopedAST bind' (substitute scope' subst body)

-- | Quote every value in a substitution's codomain, turning a semantic
-- environment into a syntactic one. Used by 'freezeScopedClosure' to substitute
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
