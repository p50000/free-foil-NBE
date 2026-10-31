{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
-- With let-generalisation, GHC reports free-foil's 'Foil.DExt' in a
-- signature as a constraint it could simplify by its instance.
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Top-level definitions, as a context: a free name may have a value, which
-- 'FreeFoil.NbE.eval' unfolds wherever the name is used (δ-reduction). A
-- program @x₁ = t₁; …; xₖ = tₖ; t@ is the context that defines @x₁ … xₖ@
-- in turn, each body in the context of the names before it, and @t@
-- normalised in that context with 'FreeFoil.NbE.nf'. The definitions are
-- non-recursive.
--
-- The values are lazy, so a body is evaluated at most once, and only when
-- its name is used. This is how Coquand evaluates @let@ ("An algorithm for
-- type-checking dependent types", 1996, §3), with the values of the defined
-- names in the context rather than in the environment: the environment maps
-- the variables a term binds, the context the names free in it, as Rzk's
-- context does for its variables. t'Defined' is the instance of
-- 'FreeFoil.NbE.Definitions' that holds them, as a free-foil substitution
-- over the context's scope.
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

import           FreeFoil.NbE                (Context (..), Definitions (..), Eval, Value, eval)

-- | A context of definitions: a scope and the values of the names it
-- defines, a substitution over the scope that maps every other name to
-- itself.
data Defined binder sig n = Defined (Foil.Scope n) (Foil.Substitution (Value binder sig) n n)

instance Bifunctor sig => Context (Defined binder sig) where
  {-# INLINE contextScope #-}
  contextScope (Defined scope _) = scope
  {-# INLINE extendContext #-}
  extendContext _ scope (Defined _ subst) = Defined scope (underBinder subst)

instance Bifunctor sig => Definitions (Defined binder sig) binder sig where
  {-# INLINE definition #-}
  definition (Defined _ subst) = Foil.lookupSubst subst

-- | A substitution over a scope, under a binder of that scope. 'Foil.sink'
-- moves the values. The names the binder adds are not in the map, so they
-- map to themselves, which is how free-foil records an identity rename
-- ('Foil.addRename' stores none). So the map is rewrapped at the larger
-- input scope as it is. 'Foil.addRename' of each name to itself would do
-- the same with public functions, at the cost of a deletion per name at
-- every binder.
underBinder :: (Foil.Sinkable e, Foil.DExt n l) => Foil.Substitution e n n -> Foil.Substitution e l l
{-# INLINE underBinder #-}
underBinder subst = case Foil.sink subst of
  Foil.UnsafeSubstitution values -> Foil.UnsafeSubstitution values

-- | The context over a scope that defines none of its names.
noDefinitions :: Foil.Scope n -> Defined binder sig n
noDefinitions scope = Defined scope Foil.identitySubst

-- | The context under a binder whose name has a value.
defineValue ::
  (Bifunctor sig, Foil.DExt n l) =>
  Foil.NameBinder n l ->
  Value binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
defineValue x value (Defined scope subst) =
  Defined (Foil.extendScope x scope) (Foil.addSubst (Foil.sink subst) x (Foil.sink value))

-- | The context under a binder whose name has the value of a body. The body
-- is in the scope of the context, so it may use the names defined before,
-- and it is evaluated in the context, when the name is first used.
define ::
  (Eval (Defined binder sig) binder sig, Foil.Distinct n, Foil.DExt n l) =>
  Foil.NameBinder n l ->
  AST binder sig n ->
  Defined binder sig n ->
  Defined binder sig l
define x body ctx = defineValue x (eval ctx Foil.identitySubst body) ctx
