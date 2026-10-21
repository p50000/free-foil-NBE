{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE InstanceSigs   #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}
-- | The semantic domain with its constructors, for the library's own
-- modules. A language sees it only through "FreeFoil.NbE", which hides the
-- constructors, so that a rule can inspect a value only through
-- 'FreeFoil.NbE.eliminate'.
module FreeFoil.NbE.Internal.Value
  ( Glue (..)
  , Value' (..)
  , Value
  , Whnf
  ) where

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (ScopedAST (..))
import           Data.Bifunctor          (Bifunctor (..))
import           Data.Kind               (Type)
import           Data.Void               (Void)

-- | Whether a value may be glued at its root.
data Glue = MayGlue | NoGlue

-- | The semantic domain, indexed by whether a value may be glued at its
-- root. The index is phantom, so a 'Whnf' is a 'Value' with the same
-- representation.
data Value' (g :: Glue) binder sig (n :: Foil.S) :: Type where
  -- | A neutral variable.
  VVar_ :: {-# UNPACK #-} !(Foil.Name n) -> Value' g binder sig n
  -- | A node without scoped subterms.
  VNode_ :: sig Void (Value binder sig n) -> Value' g binder sig n
  -- | A node with scoped subterms, suspended under its environment; the
  -- environment sits in the constructor, so the node costs one heap object
  -- beside its @sig@ cell.
  VSuspended_ ::
    Foil.Distinct i =>
    Foil.Substitution (Value binder sig) i n ->
    sig (ScopedAST binder sig i) (Value binder sig n) ->
    Value' g binder sig n
  -- | A glued value: a neutral headed by a defined name, and its lazy
  -- unfolding (see "FreeFoil.NbE.Glue").
  VGlued_ :: Value binder sig n -> Value binder sig n -> Value' g binder sig n

-- | A semantic value in scope @n@. Term subterms are values already; only
-- scoped subterms, the bodies under binders, are suspended. A
-- 'FreeFoil.NbE.VSuspended' node keeps its term subterms as values, its
-- scoped subterms as syntax, and one captured environment for them all: a
-- @Pi@ holds its domain as a value while its codomain waits, unevaluated, for
-- the environment. Since 'FreeFoil.NbE.eval' and 'FreeFoil.NbE.quote' each
-- visit every subterm exactly once, readback is linear in the size of the
-- term, and nested @Pi@ types do not re-normalise their codomains.
--
-- /Invariant./ Every value 'FreeFoil.NbE.eval' produces is weak-head normal
-- at every position: no node is an eliminator applied to the introduction
-- form it eliminates. The type cannot enforce this, as it does not know which
-- constructors of @sig@ eliminate; the language's 'FreeFoil.NbE.evalSig'
-- establishes it, and every function of the library preserves it.
--
-- A rule cannot match a 'Value'. It sees one as a 'Whnf' through
-- 'FreeFoil.NbE.eliminate'.
type Value = Value' 'MayGlue

-- | A value that is not glued at its root: what an elimination rule sees.
type Whnf = Value' 'NoGlue

instance Foil.InjectName (Value' g binder sig) where
  injectName = VVar_

instance Bifunctor sig => Foil.Sinkable (Value' g binder sig) where
  sinkabilityProof :: (Foil.Name n -> Foil.Name l) -> Value' g binder sig n -> Value' g binder sig l
  sinkabilityProof rename (VVar_ x) =
    VVar_ (rename x)
  sinkabilityProof rename (VNode_ node) =
    VNode_ (bimap id (Foil.sinkabilityProof rename) node)
  sinkabilityProof rename (VSuspended_ env node) =
    VSuspended_ (Foil.sinkabilityProof rename env) (bimap id (Foil.sinkabilityProof rename) node)
  sinkabilityProof rename (VGlued_ folded unfolded) =
    VGlued_ (Foil.sinkabilityProof rename folded) (Foil.sinkabilityProof rename unfolded)
