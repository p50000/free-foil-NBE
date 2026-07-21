{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}

-- | Generic normalisation by evaluation (NbE) via free-foil.
module FreeFoil.NbE
  ( module Foil
  , module FreeFoil
  , Closure (..)
  , quote'
  , quoteScoped
  , substituteClosure
  , composeSubst
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
-- Handy for inspecting the captured environment of a 'Closure' without
-- reaching into foil internals.
substitutionDomain :: Substitution e i o -> [Int]
substitutionDomain (UnsafeSubstitution m) = IntMap.keys m

-- | A semantic value for NbE.
--
-- 'VarC' is a neutral variable (a stuck computation whose head is a free
-- variable). 'Closure' suspends a syntax node together with an environment
-- of captured variables. A neutral node (a stuck eliminator, e.g. an
-- application blocked on a variable) is represented as a 'Closure' over the
-- identity substitution, so it needs no separate constructor: evaluation
-- distinguishes redexes from neutrals by matching on the node itself.
data Closure binder sig i where
  VarC ::
    Name i -> Closure binder sig i
  Closure ::
    (Distinct i) =>
    Substitution (Closure binder sig) i o -> -- Environment of captured variables.
    sig (ScopedAST binder sig i) (Closure binder sig i) ->
    Closure binder sig o

instance Foil.InjectName (Closure pat sig) where
  injectName = VarC

instance Foil.Sinkable (Closure pat sig) where
  sinkabilityProof :: (Name n -> Name l) -> Closure pat sig n -> Closure pat sig l
  sinkabilityProof rename (VarC n) =
    VarC (rename n)
  sinkabilityProof rename (Closure env sig) =
    Closure (Foil.sinkabilityProof rename env) sig

quoteScoped ::
  ( Foil.Distinct n,
    Foil.Distinct o,
    Bifunctor sig,
    Foil.CoSinkable binder,
    Foil.HasNameBinders binder
  ) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
    Foil.Scope m ->
    Foil.Substitution (Closure binder sig) l m ->
    AST binder sig l ->
    Closure binder sig m
  ) ->
  Foil.Scope o ->
  Foil.Substitution (Closure binder sig) n o ->
  ScopedAST binder sig n ->
  ScopedAST binder sig o
quoteScoped eval scope env (ScopedAST bind body) =
  Foil.withRefreshedPattern scope bind $ \(extendEnv :: Foil.Substitution (Closure bind sig) n o -> Foil.Substitution (Closure bind sig) l o') bind' ->
    case Foil.assertDistinct bind' of
      Foil.Distinct ->
        case Foil.assertDistinct bind of
          Foil.Distinct ->
            let scope' = Foil.extendScopePattern bind' scope
                env' = extendEnv env
             in ScopedAST bind' (quote' eval scope' (eval scope' env' body))

-- | Quote a closure back into an AST node, using the provided evaluation function.
quote' ::
  (Foil.Distinct n, Bifunctor sig, Foil.HasNameBinders pat, Foil.CoSinkable pat) =>
  (forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
    Foil.Scope m ->
    Foil.Substitution (Closure pat sig) l m ->
    AST pat sig l ->
    Closure pat sig m
  ) ->
  Foil.Scope n ->
  Closure pat sig n ->
  AST pat sig n
quote' eval scope = \case
  VarC x -> Var x
  Closure (env :: Foil.Substitution (Closure pat sig) i n) node ->
    Node $
      bimap
        (quoteScoped eval scope env)
        (quote' eval scope . substituteClosure scope env)
        node


-- | Perform substitution inside a closure using the given environment and scope.
substituteClosure ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Closure pat sig n ->
  Closure pat sig o
substituteClosure _scope env (VarC x) =
  Foil.lookupSubst env x
substituteClosure scope env (Closure env' sig) =
  Closure (composeSubst scope env env') sig

-- | Compose two substitutions under a given scope to produce a combined substitution.
composeSubst ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Foil.Substitution (Closure pat sig) k n ->
  Foil.Substitution (Closure pat sig) k o
composeSubst
  scope
  env@(UnsafeSubstitution outerMap)
  (UnsafeSubstitution innerMap) =
    UnsafeSubstitution $
      IntMap.union
        (IntMap.map (substituteClosure scope env) innerMap)
        outerMap
