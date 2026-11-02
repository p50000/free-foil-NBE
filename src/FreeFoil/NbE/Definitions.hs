{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
-- With let-generalisation, GHC reports free-foil's 'Foil.DExt' in a
-- signature as a constraint it could simplify by its instance.
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Top-level definitions as a context. A program @x₁ = t₁; …; xₖ = tₖ; t@
-- is the context that defines @x₁ … xₖ@ in turn, each body in the context
-- of the names before it, and @t@ is normalised in it with
-- 'FreeFoil.NbE.nf'. The definitions are non-recursive. A body is evaluated
-- at most once, and only when its name is used.
--
-- A defined name evaluates to a glued value: the name beside the lazy value
-- of its body. This follows the glued evaluation of Kovács (smalltt, and
-- @GluedEval@ of the elaboration zoo). Readback follows the
-- context's 'Unfolding': 'Unfolded' gives the normal form, 'Folded' keeps
-- the defined names. Conversion compares glued values as smalltt does
-- ('Approximation'), whichever side readback follows.
module FreeFoil.NbE.Definitions
  ( Defined
  , Unfolding (..)
  , noDefinitions
  , withUnfolding
  , define
  , defineValue
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Name (..), Substitution (..))
import           Control.Monad.Free.Foil     (AST)
import           Data.Bifunctor              (Bifunctor)

import qualified Data.IntMap                 as IntMap

import           FreeFoil.NbE                (Eval, HasDefinitions (..), Speculation (..), Value, eval)
import           FreeFoil.NbE.Internal.Value (Value' (..))

-- | Which side of a defined name readback follows.
data Unfolding
  = Folded    -- ^ Keep the defined names.
  | Unfolded  -- ^ Unfold every definition: the normal form.

-- | The state of a conversion check, after smalltt's approximate
-- conversion checking (@unify@ in its @src/Unification.hs@). A check starts
-- 'Rigid'. Two glued values of one defined name compare their folded sides
-- 'Flex', which unfolds nothing and fails where it would have to. If that
-- fails, they compare their unfolded sides 'Full', which unfolds every
-- glued value at once and compares no folded sides again. So a check tries
-- the folded sides at most once on any path to a subterm.
data Approximation = Rigid | Flex | Full

-- | A context of definitions: the values of the names it defines, the side
-- of a defined name that readback follows, and the state of conversion.
data Defined binder sig n = Defined
  { definedUnfolding     :: Unfolding
  , definedApproximation :: Approximation
  , definedValues        :: Foil.Substitution (Value binder sig) n n
  }

-- | Under a binder the context defines the same names. The keys are renamed
-- through free-foil's internal constructor, as free-foil does for
-- 'Foil.NameSet', since free-foil has no instance for a substitution from a
-- scope to itself.
instance Bifunctor sig => Foil.Sinkable (Defined binder sig) where
  sinkabilityProof rename (Defined unfolding approximation (Foil.UnsafeSubstitution values)) =
    Defined unfolding approximation (Foil.UnsafeSubstitution (IntMap.fromList
      [ (Foil.nameId (rename (Foil.UnsafeName k)), Foil.sinkabilityProof rename v)
      | (k, v) <- IntMap.toList values ]))

-- | A defined name is glued to its value, any other name is a neutral.
-- Conversion follows smalltt's states ('Approximation').
instance Bifunctor sig => HasDefinitions (Defined binder sig) binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ (Defined _ _ (Foil.UnsafeSubstitution values)) x =
    case IntMap.lookup (Foil.nameId x) values of
      Just value -> VGlued_ x (VVar_ x) value
      Nothing    -> VVar_ x
  {-# INLINE contextUnfolding #-}
  contextUnfolding _ ctx folded unfolded = case definedUnfolding ctx of
    Folded   -> folded
    Unfolded -> unfolded
  {-# INLINE contextSpeculation #-}
  contextSpeculation _ ctx x _ y _ = case definedApproximation ctx of
    Rigid
      | x == y    -> Speculate (ctx { definedApproximation = Flex }) (Just (ctx { definedApproximation = Full }))
      | otherwise -> Unfold ctx
    Flex
      | x == y    -> Speculate ctx Nothing
      | otherwise -> Unrelated
    Full -> Unfold ctx
  {-# INLINE contextUnfoldAgainst #-}
  contextUnfoldAgainst _ ctx _ _ = case definedApproximation ctx of
    Flex -> Nothing
    _    -> Just ctx

-- | The context that defines no names, whose readback unfolds every
-- definition.
noDefinitions :: Defined binder sig n
noDefinitions = Defined Unfolded Rigid Foil.identitySubst

-- | The same definitions, read back on the given side.
withUnfolding :: Unfolding -> Defined binder sig n -> Defined binder sig n
withUnfolding unfolding ctx = ctx { definedUnfolding = unfolding }

-- | The context under a binder whose name has a value.
defineValue ::
  (Bifunctor sig, Foil.DExt n l) =>
  Foil.NameBinder n l ->
  Value binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
defineValue x value ctx =
  ctx { definedValues = Foil.addSubst (Foil.sink (definedValues ctx)) x (Foil.sink value) }

-- | The context under a binder whose name has the value of a body. The body
-- may use the names defined before, and is evaluated when the name is first
-- used.
define ::
  (Eval (Defined binder sig) binder sig, Foil.Distinct n, Foil.DExt n l) =>
  Foil.Scope n ->
  Foil.NameBinder n l ->
  AST binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
define scope x body ctx = defineValue x (eval scope ctx Foil.identitySubst body) ctx
