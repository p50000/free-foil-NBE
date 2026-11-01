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
import qualified Control.Monad.Foil.Internal as Foil (Substitution (..))
import           Control.Monad.Free.Foil     (AST)
import           Data.Bifunctor              (Bifunctor)

import           FreeFoil.NbE                (Context (..), Eval, HasDefinitions (..), Value, eval)

-- | A context of definitions: the values of the names it defines.
newtype Defined binder sig n = Defined (Foil.Substitution (Value binder sig) n n)

instance Bifunctor sig => Context (Defined binder sig) where
  {-# INLINE extendContext #-}
  extendContext _ _ _ (Defined subst) = Defined (underBinder subst)

instance Bifunctor sig => HasDefinitions (Defined binder sig) binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ (Defined subst) = Foil.lookupSubst subst

-- | A substitution over a scope, under a binder of that scope. The names the
-- binder adds are not in the map, so they map to themselves, and the map is
-- reused at the larger input scope. 'Foil.addRename' would do the same with
-- public functions, at the cost of a deletion per name at every binder. The
-- function belongs in free-foil.
underBinder :: (Foil.Sinkable e, Foil.DExt n l) => Foil.Substitution e n n -> Foil.Substitution e l l
{-# INLINE underBinder #-}
underBinder subst = case Foil.sink subst of
  Foil.UnsafeSubstitution values -> Foil.UnsafeSubstitution values

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
