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
module FreeFoil.NbE.Definitions
  ( Defined
  , noDefinitions
  , define
  , defineValue
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Name (..), Substitution (..))
import           Control.Monad.Free.Foil     (AST)
import           Data.Bifunctor              (Bifunctor)

import qualified Data.IntMap                 as IntMap

import           FreeFoil.NbE                (Eval, HasDefinitions (..), Value, eval)

-- | A context of definitions: the values of the names it defines.
newtype Defined binder sig n = Defined (Foil.Substitution (Value binder sig) n n)

-- | Under a binder the context defines the same names. The keys are renamed
-- through free-foil's internal constructor, as free-foil does for
-- 'Foil.NameSet', since free-foil has no instance for a substitution from a
-- scope to itself.
instance Bifunctor sig => Foil.Sinkable (Defined binder sig) where
  sinkabilityProof rename (Defined (Foil.UnsafeSubstitution values)) =
    Defined (Foil.UnsafeSubstitution (IntMap.fromList
      [ (Foil.nameId (rename (Foil.UnsafeName k)), Foil.sinkabilityProof rename v)
      | (k, v) <- IntMap.toList values ]))

instance Bifunctor sig => HasDefinitions (Defined binder sig) binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ (Defined subst) = Foil.lookupSubst subst

-- | The context that defines no names.
noDefinitions :: Defined binder sig n
noDefinitions = Defined Foil.identitySubst

-- | The context under a binder whose name has a value.
defineValue ::
  (Bifunctor sig, Foil.DExt n l) =>
  Foil.NameBinder n l ->
  Value binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
defineValue x value (Defined subst) =
  Defined (Foil.addSubst (Foil.sink subst) x (Foil.sink value))

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
