{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Glued evaluation: a defined name evaluates to a value that keeps the name
-- next to a lazy unfolding, so that readback can keep definitions folded and
-- conversion checking can compare them folded first. This follows the glued
-- evaluation of Kovács (smalltt, and @GluedEval@ of the elaboration zoo).
--
-- The rules of a language see through glue with 'FreeFoil.NbE.eliminate',
-- 'FreeFoil.NbE.Conversion.conv' compares glued values folded first, and
-- "FreeFoil.NbE.Definitions" makes them. This module reads them back.
module FreeFoil.NbE.Glue
  ( Unfolding (..)
  , quoteGlued
  ) where

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..))
import           Data.Bifunctor              (bimap)
import           Data.Void                   (absurd)

import           FreeFoil.NbE                (Eval, Value, eval)
import           FreeFoil.NbE.Internal.Value (Value' (..))

-- | Which side of a glued value readback follows.
data Unfolding
  = Folded    -- ^ Keep the defined names.
  | Unfolded  -- ^ Unfold every definition: the normal form.

-- | Read a value back following one side of every glued value; otherwise the
-- core's 'FreeFoil.NbE.quote', with its scoped case, which evaluates the body
-- once under the refreshed binder, so that glue keeps propagating under
-- binders.
quoteGlued ::
  forall binder sig n.
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Unfolding ->
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quoteGlued #-}
quoteGlued mode = go
  where
    go :: forall m. Foil.Distinct m => Foil.Scope m -> Value binder sig m -> AST binder sig m
    go scope = \case
      VGlued_ folded unfolded ->
        go scope $ case mode of
          Folded   -> folded
          Unfolded -> unfolded
      VVar_ x -> Var x
      VNode_ node -> Node $! bimap absurd (go scope) node
      VSuspended_ env node -> Node $! bimap (goScoped scope env) (go scope) node

    goScoped ::
      forall m i. (Foil.Distinct m, Foil.Distinct i) =>
      Foil.Scope m -> Foil.Substitution (Value binder sig) i m -> ScopedAST binder sig i -> ScopedAST binder sig m
    goScoped scope env (ScopedAST binder body) =
      Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
        case Foil.assertDistinct binder of
          Foil.Distinct -> ScopedAST binder' (go scope' (eval scope' (extendEnv env) body))
