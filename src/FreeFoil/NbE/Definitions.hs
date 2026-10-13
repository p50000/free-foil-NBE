{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
-- | Top-level definitions: a program is a telescope of definitions
-- @x₁ = t₁; …; xₖ = tₖ@ followed by a term, where each body may use the
-- names defined before it. The definitions are non-recursive.
--
-- Definitions need nothing new from the core. The values of the bodies form
-- the initial environment of 'eval', which maps each defined name to the
-- value of its body (δ-reduction). The environment is lazy, so a body is
-- evaluated at most once, and only when its name is used. This is how
-- Coquand evaluates @let@ ("An algorithm for type-checking dependent types",
-- 1996, §3), and how Renata Shakirova's "LambdaLet" demo evaluates its local
-- @let@.
module FreeFoil.NbE.Definitions
  ( Definitions (..)
  , definitionsEnv
  , evalUnfolded
  , nfUnfolded
  ) where

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (AST)

import           FreeFoil.NbE            (Eval, Value, eval, quote)

-- | A telescope of definitions that extends scope @n@ to scope @l@. The body
-- of each definition is in the scope of the names defined before it.
data Definitions binder sig n l where
  NoDefinitions :: Definitions binder sig n n
  Define ::
    (Foil.Distinct m, Foil.DExt m l) =>
    Definitions binder sig n m ->
    Foil.NameBinder m l ->
    AST binder sig m ->
    Definitions binder sig n l

-- | The environment of a telescope: each defined name maps to the value of
-- its body, and the names of @n@ map to themselves.
definitionsEnv ::
  (Eval binder sig, Foil.Distinct n) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  Foil.Substitution (Value binder sig) l n
{-# INLINABLE definitionsEnv #-}
definitionsEnv _ NoDefinitions = Foil.identitySubst
definitionsEnv scope (Define defs x body) =
  let env = definitionsEnv scope defs
  in Foil.addSubst env x (eval scope env body)

-- | Evaluate a term in the scope of a telescope, unfolding every definition.
evalUnfolded ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct l) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  AST binder sig l ->
  Value binder sig n
{-# INLINABLE evalUnfolded #-}
evalUnfolded scope defs = eval scope (definitionsEnv scope defs)

-- | The normal form of a term with every definition unfolded: the normal form
-- of the term with each defined name replaced by its body.
nfUnfolded ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct l, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  AST binder sig l ->
  AST binder sig n
{-# INLINABLE nfUnfolded #-}
nfUnfolded scope defs = quote scope . evalUnfolded scope defs
