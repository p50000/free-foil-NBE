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
-- the defined names. Conversion compares defined names folded first either
-- way.
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

import           FreeFoil.NbE                (Eval, HasDefinitions (..), Value, eval)
import           FreeFoil.NbE.Internal.Value (Value' (..))

-- | Which side of a defined name readback follows.
data Unfolding
  = Folded    -- ^ Keep the defined names.
  | Unfolded  -- ^ Unfold every definition: the normal form.

-- | A context of definitions: the values of the names it defines, and the
-- side of a defined name that readback follows.
data Defined binder sig n = Defined Unfolding (Foil.Substitution (Value binder sig) n n)

-- | Under a binder the context defines the same names. The keys are renamed
-- through free-foil's internal constructor, as free-foil does for
-- 'Foil.NameSet', since free-foil has no instance for a substitution from a
-- scope to itself.
instance Bifunctor sig => Foil.Sinkable (Defined binder sig) where
  sinkabilityProof rename (Defined unfolding (Foil.UnsafeSubstitution values)) =
    Defined unfolding (Foil.UnsafeSubstitution (IntMap.fromList
      [ (Foil.nameId (rename (Foil.UnsafeName k)), Foil.sinkabilityProof rename v)
      | (k, v) <- IntMap.toList values ]))

-- | A defined name is glued to its value, any other name is a neutral.
instance Bifunctor sig => HasDefinitions (Defined binder sig) binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ (Defined _ (Foil.UnsafeSubstitution values)) x =
    case IntMap.lookup (Foil.nameId x) values of
      Just value -> VGlued_ x (VVar_ x) value
      Nothing    -> VVar_ x
  {-# INLINE contextUnfolding #-}
  contextUnfolding _ (Defined unfolding _) folded unfolded = case unfolding of
    Folded   -> folded
    Unfolded -> unfolded

-- | The context that defines no names, whose readback unfolds every
-- definition.
noDefinitions :: Defined binder sig n
noDefinitions = Defined Unfolded Foil.identitySubst

-- | The same definitions, read back on the given side.
withUnfolding :: Unfolding -> Defined binder sig n -> Defined binder sig n
withUnfolding unfolding (Defined _ subst) = Defined unfolding subst

-- | The context under a binder whose name has a value.
defineValue ::
  (Bifunctor sig, Foil.DExt n l) =>
  Foil.NameBinder n l ->
  Value binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
defineValue x value (Defined unfolding subst) =
  Defined unfolding (Foil.addSubst (Foil.sink subst) x (Foil.sink value))

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
