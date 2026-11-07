{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}
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
  , relateNodesF
  ) where

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (AST, ScopedAST)
import           Data.Bifoldable         (Bifoldable)
import           Data.Bifunctor          (Bifunctor (..))
import           Control.Applicative     ((<|>))
import           Data.Bifunctor.Sum      (Sum (..))
import           Data.Maybe              (fromMaybe)
import           Data.ZipMatchK          (ZipMatchFoldK)

import           FreeFoil.NbE            (EtaScoped, EtaTerm, Eval (..), Extend, HasDefinitions, HasHeads, Value, evalNode, relateExtended, sinkExtend, vvar)

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
class (Bifunctor f, Bifoldable f, HasHeads f) => EvalF ctx binder f where
  evalF ::
    (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
    Inj f sig ->
    Foil.Scope o ->
    ctx o ->
    Foil.Substitution (Value binder sig) i o ->
    f (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalF pos scope ctx env node = evalNode scope ctx env (inj pos node)

  -- | The η laws of the fragment's introduction forms at a position, as
  -- 'etaMatchWith'. By default there are none.
  etaMatchWithF ::
    Inj f sig ->
    (a -> EtaScoped ctx binder sig n -> c) ->
    (b -> EtaTerm ctx binder sig n -> d) ->
    f a b ->
    Maybe (f c d)
  {-# INLINE etaMatchWithF #-}
  etaMatchWithF _ _ _ _ = Nothing

  -- | The context under the binders of the fragment's scoped positions at a
  -- position, as 'extendScopedWith'. By default a binder only adds its
  -- names.
  extendScopedWithF ::
    Foil.Distinct n =>
    Inj f sig ->
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    f a (Value binder sig n) ->
    f c d
  default extendScopedWithF ::
    (Foil.Sinkable ctx, Foil.Distinct n) =>
    Inj f sig ->
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    f a (Value binder sig n) ->
    f c d
  {-# INLINE extendScopedWithF #-}
  extendScopedWithF _ scoped term = bimap (\a -> scoped a sinkExtend) term

  -- | Refine a variable of the language, as 'refineVar', or 'Nothing' if
  -- the fragment has nothing to say about it. Refinement follows types,
  -- not the fragment of a node: the fragment of the function type
  -- η-expands every function. So the method sees the variables of the
  -- whole language, and a sum takes the first summand that refines. By
  -- default the fragment refines nothing.
  refineVarF ::
    (Eval ctx binder sig, Foil.Distinct n) =>
    Inj f sig ->
    Foil.Scope n ->
    ctx n ->
    Foil.Name n ->
    Maybe (Value binder sig n)
  {-# INLINE refineVarF #-}
  refineVarF _ _ _ _ = Nothing

  -- | Refine a node of the language, as 'refineSig', like 'refineVarF'.
  refineSigF ::
    (Eval ctx binder sig, Foil.Distinct n) =>
    Inj f sig ->
    Foil.Scope n ->
    ctx n ->
    Value binder sig n ->
    sig a (Value binder sig n) ->
    Maybe (Value binder sig n)
  {-# INLINE refineSigF #-}
  refineSigF _ _ _ _ _ = Nothing

  -- | Whether the context makes two values of the language equal that
  -- conversion has found different, as 'relateMismatch'. Like 'refineVarF',
  -- the method sees the values of the whole language, and a sum relates
  -- them if one of its summands does. By default the fragment relates none.
  relateMismatchF ::
    (Eval ctx binder sig, Foil.Distinct n) =>
    Inj f sig ->
    Foil.Scope n ->
    ctx n ->
    Value binder sig n ->
    Value binder sig n ->
    Bool
  {-# INLINE relateMismatchF #-}
  relateMismatchF _ _ _ _ _ = False

  -- | How conversion compares two nodes of the fragment at a position, as
  -- 'relateWith' does for a language.
  relateWithF ::
    (Monoid m, Foil.Distinct n) =>
    Inj f sig ->
    Foil.Scope n ->
    ctx n ->
    (a -> a' -> ctx n -> Extend ctx binder sig n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    f a (Value binder sig n) ->
    f a' (Value binder sig n) ->
    Maybe m
  default relateWithF ::
    (ZipMatchFoldK f, Monoid m, Foil.Distinct n) =>
    Inj f sig ->
    Foil.Scope n ->
    ctx n ->
    (a -> a' -> ctx n -> Extend ctx binder sig n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    f a (Value binder sig n) ->
    f a' (Value binder sig n) ->
    Maybe m
  {-# INLINE relateWithF #-}
  relateWithF pos scope ctx scoped term hd l r = relateNodesF pos scope ctx scoped term hd l r

-- | The default of 'relateWithF', as 'FreeFoil.NbE.relateNodes' is for a
-- language: a fragment's own cases fall back on it.
relateNodesF ::
  (EvalF ctx binder f, ZipMatchFoldK f, Monoid m, Foil.Distinct n) =>
  Inj f sig ->
  Foil.Scope n ->
  ctx n ->
  (a -> a' -> ctx n -> Extend ctx binder sig n -> m) ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  f a (Value binder sig n) ->
  f a' (Value binder sig n) ->
  Maybe m
{-# INLINE relateNodesF #-}
relateNodesF pos _ ctx scoped term hd l r =
  relateExtended ctx term hd (extendScopedWithF pos (\a extend a' ctx' -> scoped a a' ctx' extend) id l) r

-- | The rules of a sum are the rules of its summands.
instance (EvalF ctx binder f, EvalF ctx binder g) => EvalF ctx binder (Sum f g) where
  {-# INLINE evalF #-}
  evalF pos scope ctx env = \case
    L2 node -> evalF (inL pos) scope ctx env node
    R2 node -> evalF (inR pos) scope ctx env node
  {-# INLINE etaMatchWithF #-}
  etaMatchWithF pos scoped term = \case
    L2 node -> L2 <$> etaMatchWithF (inL pos) scoped term node
    R2 node -> R2 <$> etaMatchWithF (inR pos) scoped term node
  {-# INLINE extendScopedWithF #-}
  extendScopedWithF pos scoped term = \case
    L2 node -> L2 (extendScopedWithF (inL pos) scoped term node)
    R2 node -> R2 (extendScopedWithF (inR pos) scoped term node)
  {-# INLINE refineVarF #-}
  refineVarF pos scope ctx x =
    refineVarF (inL pos) scope ctx x <|> refineVarF (inR pos) scope ctx x
  {-# INLINE refineSigF #-}
  refineSigF pos scope ctx value node =
    refineSigF (inL pos) scope ctx value node <|> refineSigF (inR pos) scope ctx value node
  {-# INLINE relateMismatchF #-}
  relateMismatchF pos scope ctx l r =
    relateMismatchF (inL pos) scope ctx l r || relateMismatchF (inR pos) scope ctx l r
  {-# INLINE relateWithF #-}
  relateWithF pos scope ctx scoped term hd l r = case (l, r) of
    (L2 a, L2 b) -> relateWithF (inL pos) scope ctx scoped term hd a b
    (R2 a, R2 b) -> relateWithF (inR pos) scope ctx scoped term hd a b
    _            -> Nothing

-- | A sum of fragments is a language: its rules are those of the sum at the
-- root position.
instance (HasDefinitions ctx binder (Sum f g), EvalF ctx binder f, EvalF ctx binder g) => Eval ctx binder (Sum f g) where
  {-# INLINE evalSig #-}
  evalSig = evalF root
  {-# INLINE etaMatchWith #-}
  etaMatchWith scoped term = etaMatchWithF root scoped term
  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term = extendScopedWithF root scoped term
  {-# INLINE refineVar #-}
  refineVar scope ctx x = fromMaybe (vvar x) (refineVarF root scope ctx x)
  {-# INLINE refineSig #-}
  refineSig scope ctx value node = fromMaybe value (refineSigF root scope ctx value node)
  {-# INLINE relateWith #-}
  relateWith = relateWithF root
  {-# INLINE relateMismatch #-}
  relateMismatch = relateMismatchF root
