{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}

-- | Generic normalisation by evaluation (NbE) via free-foil.
module FreeFoil.NbE
  ( module Foil
  , module FreeFoil
  , Value (..)
  , ScopedClosure (..)
  , quote
  , quoteScopedClosure
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
-- variable). 'VNode' is a fully evaluated syntax node whose /term/ subterms
-- are themselves values (already in the ambient scope @n@) and whose /scoped/
-- subterms are 'ScopedClosure's — suspended bodies that each carry their own
-- captured environment. A neutral node (a stuck eliminator, e.g. an
-- application blocked on a variable) is just a 'VNode' whose head is neutral;
-- evaluation distinguishes redexes from neutrals by matching on the node.
--
-- Because term subterms are already values, every subterm is evaluated and
-- quoted exactly once. This is what keeps 'quote' linear in the term size —
-- in particular, nested 'Pi' types do not re-normalise their codomains.
data Value binder sig n where
  VVar ::
    Name n -> Value binder sig n
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

-- | Quote a value back into an AST, using the provided evaluation function.
-- Each subterm is processed exactly once: term subterms recurse directly,
-- scoped subterms are read back under their binder via 'quoteScopedClosure'.
quote ::
  (Foil.Distinct n, Bifunctor sig, Foil.HasNameBinders pat, Foil.CoSinkable pat) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
    Foil.Scope m ->
    Foil.Substitution (Value pat sig) l m ->
    AST pat sig l ->
    Value pat sig m
  ) ->
  Foil.Scope n ->
  Value pat sig n ->
  AST pat sig n
quote eval scope = \case
  VVar x -> Var x
  VNode node ->
    Node $
      bimap
        (quoteScopedClosure eval scope)
        (quote eval scope)
        node

-- | Read back a suspended scoped subterm: refresh the binder, extend the
-- captured environment to map it to a fresh neutral, evaluate the body once
-- under that environment, and quote the result.
quoteScopedClosure ::
  ( Foil.Distinct n,
    Bifunctor sig,
    Foil.CoSinkable binder,
    Foil.HasNameBinders binder
  ) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
    Foil.Scope m ->
    Foil.Substitution (Value binder sig) l m ->
    AST binder sig l ->
    Value binder sig m
  ) ->
  Foil.Scope n ->
  ScopedClosure binder sig n ->
  ScopedAST binder sig n
quoteScopedClosure eval scope (ScopedClosure env (ScopedAST bind body)) =
  Foil.withRefreshedPattern scope bind $ \extendEnv bind' ->
    case Foil.assertDistinct bind' of
      Foil.Distinct ->
        case Foil.assertDistinct bind of
          Foil.Distinct ->
            let scope' = Foil.extendScopePattern bind' scope
                env' = extendEnv env
             in ScopedAST bind' (quote eval scope' (eval scope' env' body))
