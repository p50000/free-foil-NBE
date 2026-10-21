{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
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
--
-- With glue ("FreeFoil.NbE.Glue"), 'withDefinitions' maps each name to a
-- glued value instead, the name itself beside the lazy value of its body, and
-- the result is read back either folded, keeping the defined names wherever
-- no rule needed their bodies, or unfolded.
module FreeFoil.NbE.Definitions
  ( Definitions (..)
    -- * Unfolded
  , definitionsEnv
  , evalUnfolded
  , nfUnfolded
    -- * Glued
  , withDefinitions
  , nfWith
  , nfFolded
  , convertibleIn
  ) where

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Free.Foil     (AST)
import           Data.ZipMatchK              (ZipMatchK)

import           FreeFoil.NbE                (Eval, Value, eval, quote)
import           FreeFoil.NbE.Conversion     (convertibleUnder)
import           FreeFoil.NbE.Glue           (Unfolding (..), quoteGlued)
import           FreeFoil.NbE.Internal.Value (Value' (..))

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

-- | The environment of a telescope in the scope of its own names: each name
-- maps to a glued value, the name itself on the folded side and the lazy
-- value of its body on the unfolded side.
withDefinitions ::
  (Eval binder sig, Foil.Distinct n) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  (Foil.Distinct l => Foil.Scope l -> Foil.Substitution (Value binder sig) l l -> r) ->
  r
{-# INLINABLE withDefinitions #-}
withDefinitions scope NoDefinitions k = k scope Foil.identitySubst
withDefinitions scope (Define defs x body) k =
  withDefinitions scope defs $ \scope' env ->
    let value = Foil.sink (eval scope' env body)
        value' = VGlued_ (VVar_ (Foil.nameOf x)) value
    in k (Foil.extendScope x scope') (Foil.addSubst (Foil.sink env) x value')

-- | The normal form of a term under a telescope, read back folded or
-- unfolded, in the scope of the defined names.
nfWith ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Unfolding ->
  Foil.Scope n ->
  Definitions binder sig n l ->
  AST binder sig l ->
  AST binder sig l
{-# INLINABLE nfWith #-}
nfWith mode scope defs t =
  withDefinitions scope defs $ \scope' env -> quoteGlued mode scope' (eval scope' env t)

-- | The folded normal form: a defined name stays wherever no rule needed its
-- body.
nfFolded ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  AST binder sig l ->
  AST binder sig l
{-# INLINABLE nfFolded #-}
nfFolded = nfWith Folded

-- | Two terms are convertible under a telescope. Defined names are compared
-- folded first.
convertibleIn ::
  (Eval binder sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Definitions binder sig n l ->
  AST binder sig l ->
  AST binder sig l ->
  Bool
{-# INLINABLE convertibleIn #-}
convertibleIn scope defs t u =
  withDefinitions scope defs $ \scope' env -> convertibleUnder scope' env env t u
