{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
-- The Eval instance for a sum of fragments is an orphan on purpose: it
-- belongs with 'EvalF', which the core does not know.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Elimination rules à la carte. A language is a 'Sum' of fragments. A
-- fragment gives its rules once, through 'EvalF', for any language that
-- contains it, and the 'Eval' instance of a sum composes the rules of its
-- summands. So a composed language needs no code of its own beyond the sum.
--
-- This carries the term reduction à la carte of Kudasov's free scoped monads
-- ("Free Monads, Intrinsic Scoping, and Higher-Order Preunification", TFP
-- 2024, §3) over from terms to values: there a fragment's @reduceL@ is written
-- against @Sum t ext@ and the instance for @Sum@ composes; here a fragment's
-- rules are written for any language in which the fragment sits at a given
-- position. The position is passed as a value, 'Inj', the injection and
-- projection of Swierstra's data types à la carte as a record rather than a
-- class, so that every call is known once the language is fixed. The
-- signatures are summed with 'Sum' as in free-foil's own λΠ
-- ("Language.LambdaPi.Impl.FreeFoil", @LambdaPiF :+: PairF@).
module FreeFoil.NbE.Sum
  ( Inj (..)
  , root
  , inL
  , inR
  , EvalF (..)
  ) where

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (AST, ScopedAST)
import           Data.Bifoldable         (Bifoldable)
import           Data.Bifunctor          (Bifunctor)
import           Data.Bifunctor.Sum      (Sum (..))

import           FreeFoil.NbE            (Eval (..), Value, evalNode)

-- | The position of a fragment @f@ in a language @sig@: how to build one of
-- its nodes in the language and how to recognise one. This is Swierstra's
-- injection and projection as a record rather than a class: the instance of
-- 'EvalF' for 'Sum' computes the position of each summand as it descends
-- ('inL', 'inR'), which a class would have to find by instance search over
-- the shape of the sum, with overlapping instances once a fragment may occur
-- twice; and with the record every call is known once the language is
-- fixed.
data Inj f sig = Inj
  { inj :: forall s t. f s t -> sig s t
  , prj :: forall s t. sig s t -> Maybe (f s t)
  }

-- | A fragment on its own.
root :: Inj f f
{-# INLINE root #-}
root = Inj id Just

-- | The left summand of a sum at a position.
inL :: Inj (Sum f g) sig -> Inj f sig
{-# INLINE inL #-}
inL (Inj i p) = Inj (i . L2) (\node -> p node >>= \case
  L2 x -> Just x
  R2 _ -> Nothing)

-- | The right summand of a sum at a position.
inR :: Inj (Sum f g) sig -> Inj g sig
{-# INLINE inR #-}
inR (Inj i p) = Inj (i . R2) (\node -> p node >>= \case
  R2 x -> Just x
  L2 _ -> Nothing)

-- | The elimination rules of a fragment, for any language @sig@ in which it
-- sits at position @pos@. Like 'evalSig', 'evalF' receives the raw node and
-- the environment, matches its eliminators and evaluates the principal
-- subterm with the language's 'eval'; it recognises its own introduction
-- forms in the result with 'prj' and rebuilds a stuck node with 'inj'. Every
-- other node falls through to 'evalNode' on the injected node, which is the
-- default for a fragment without eliminators.
class (Bifunctor f, Bifoldable f) => EvalF binder f where
  evalF ::
    (Eval binder sig, Foil.Distinct o, Foil.Distinct i) =>
    Inj f sig ->
    Foil.Scope o ->
    Foil.Substitution (Value binder sig) i o ->
    f (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalF pos scope env node = evalNode scope env (inj pos node)

-- | The rules of a sum are the rules of its summands.
instance (EvalF binder f, EvalF binder g) => EvalF binder (Sum f g) where
  {-# INLINE evalF #-}
  evalF pos scope env = \case
    L2 node -> evalF (inL pos) scope env node
    R2 node -> evalF (inR pos) scope env node

-- | A sum of fragments is a language: its rules are those of the sum at the
-- root position.
instance (EvalF binder f, EvalF binder g) => Eval binder (Sum f g) where
  {-# INLINE evalSig #-}
  evalSig = evalF root
