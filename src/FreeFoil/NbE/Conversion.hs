{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Conversion checking: decide whether two values have the same normal form
-- up to renaming of bound variables and η, without reading them back.
--
-- This follows the conversion algorithm of Coquand, "An algorithm for
-- type-checking dependent types" (1996, §2.3.2 and Appendix A), with the
-- untyped η for surjective pairs of Abel and Coquand, "Untyped algorithmic
-- equality for Martin-Löf's logical framework with surjective pairs" (2007).
--
-- The check walks both values together and matches nodes with the language's
-- 'FreeFoil.NbE.relateWith', by default with free-foil's 'ZipMatchFoldK', as
-- free-foil's 'Control.Monad.Free.Foil.alphaEquiv' does for terms. Under a
-- binder it evaluates both bodies with the same fresh
-- names, but only when the comparison gets there, and it stops at the first
-- mismatch. So it can tell two terms apart even when one of them has no
-- normal form, and on convertible terms it does the work of normalisation
-- minus readback.
--
-- Two values of different shapes are compared by η when either is an
-- introduction form with an η law ('FreeFoil.NbE.etaMatchWith'): each
-- position of that form against the other value observed at that position.
-- So @λx. f x@ against @f@ compares, under a fresh @x'@, the body @f x'@
-- with @f@ applied to @x'@, and @(fst p, snd p)@ against @p@ compares the
-- components with the projections of @p@. Each step expands one layer, and
-- the positions are compared by the same check, so η applies again inside
-- them: @λx. λy. f x y@ against @f@ takes two steps. The check keeps the
-- sides: when the introduction form is on the right, each of its positions
-- is on the right of its comparison.
--
-- The check is a relation of a left value to a right one. It is conversion
-- unless the language's 'FreeFoil.NbE.relateWith' says otherwise: a language
-- whose context records the direction of the check, as Rzk's does, makes it a
-- check of subtyping.
--
-- Like the normaliser, the check is untyped and intensional: it decides β,
-- the language's own reductions, and η for the forms the language marks,
-- and it is specified on well-typed terms. η evaluates a lambda's body
-- against a neutral, so @λx. x@ against @λx. λy. Ω@ diverges, whereas
-- against @λx. (y : x) -> Ω@ it answers at once, @Pi@ having no η law.
module FreeFoil.NbE.Conversion
  ( conv
  , convertible
  , convertibleUnder
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (unsafeUnifiablePatterns)
import           Control.Monad.Free.Foil     (AST, ScopedAST (..))
import           Data.Bifoldable             (biall, biand)
import           Data.Monoid                 (All (..))
import           Data.Void                   (absurd)

import           FreeFoil.NbE                (EtaScoped (..), EtaTerm (..), Eval (..), Extend (..), Value (..), eval, refine)

-- | Two values are convertible: their normal forms are equal up to renaming
-- of bound variables and η. Nodes match when 'relateWith' matches them, by
-- default when they have the same constructor, and then their subterms are
-- compared left to right.
conv ::
  forall ctx binder sig n.
  (Eval ctx binder sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINABLE conv #-}
conv scope ctx l0 r0 = sameHead scope ctx (refine scope ctx l0) (refine scope ctx r0)
  where
    -- Two values compared without refining them: heads ('headsWith'), or
    -- values refined already. Their heads are compared the same way, every
    -- other position with 'conv'. The function is local, so that a
    -- specialisation of 'conv' covers it. It closes over nothing, so that it
    -- is not allocated at every call.
    sameHead :: Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool
    sameHead scope' ctx' l r = case (l, r) of
      (VVar x, VVar y) -> x == y
      (VNode a, VNode b)
        | Just (All same) <- relateWith scope' ctx' (\v _ _ _ -> absurd v) (other scope') (heads scope') a b -> same
      -- The language pairs the positions of the two nodes, gives each
      -- scoped pair its extension of the context and each term pair its
      -- context.
      (VSuspended envL a, VSuspended envR b)
        | Just (All same) <- relateWith scope' ctx'
            (\x y ctx'' extend -> All (convScoped scope' ctx'' envL envR x extend y)) (other scope') (heads scope') a b -> same
      -- Nodes that do not match are compared by η. A node goes to 'VNode'
      -- exactly when it has no scoped subterms, so a 'VNode' and a
      -- 'VSuspended' never have the same constructor.
      _ -> convEta scope' ctx' OnLeft l r || convEta scope' ctx' OnRight r l

    -- A pair of term positions in its context: a head ('headsWith') or
    -- another position.
    heads, other :: Foil.Distinct l => Foil.Scope l -> Value binder sig l -> Value binder sig l -> ctx l -> All
    {-# INLINE heads #-}
    heads scope' l r ctx' = All (sameHead scope' ctx' l r)
    {-# INLINE other #-}
    other scope' l r ctx' = All (conv scope' ctx' l r)

-- | The side of the comparison on which the introduction form of η stands.
data Side = OnLeft | OnRight

-- | One step of η: each position of an introduction form with an η law
-- against the other value observed at that position, on the side of the
-- introduction form. 'False' for any other value.
convEta ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  Side ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINE convEta #-}
convEta scope ctx side intro other = case intro of
  VNode node ->
    maybe False (biall absurd id) (etaMatchWith (\v _ -> absurd v) observedTerm node)
  VSuspended env node ->
    maybe False biand (etaMatchWith ($) observedTerm (extendScopedWith (convObserved scope ctx side env other) id node))
  VVar _ -> False
  where
    observedTerm v (EtaTerm observe) = sides side (conv scope ctx) v (observe scope ctx other)

-- | A comparison with the introduction form's position on the given side.
sides :: Side -> (a -> a -> b) -> a -> a -> b
{-# INLINE sides #-}
sides side compare' intro observed = case side of
  OnLeft  -> compare' intro observed
  OnRight -> compare' observed intro

-- | A scoped position of an introduction form against the other value
-- observed under the position's refreshed binder, in the context of the
-- position's extension, with the position on the side of the introduction
-- form.
convObserved ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  Side ->
  Foil.Substitution (Value binder sig) i n ->
  Value binder sig n ->
  ScopedAST binder sig i ->
  Extend ctx binder sig n ->
  EtaScoped ctx binder sig n ->
  Bool
{-# INLINE convObserved #-}
convObserved scope ctx side env other (ScopedAST binder body) (Extend extend) (EtaScoped observe) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let ctx' = extend scope binder' scope' ctx
        in sides side (conv scope' ctx')
             (eval scope' ctx' (extendEnv env) body)
             (observe scope' ctx' binder' (Foil.sink other))

-- | Compare two scoped subterms under their environments. Their binders must
-- have the same shape; they come from different scopes, so free-foil's
-- 'Foil.unsafeUnifiablePatterns' compares them. The left binder is refreshed
-- for the common scope, the names it binds extend both environments (the
-- right one by position in the pattern), the context is extended as
-- 'relateWith' says, and the bodies are compared with 'convertibleUnder'.
convScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  ScopedAST binder sig i1 ->
  Extend ctx binder sig n ->
  ScopedAST binder sig i2 ->
  Bool
{-# INLINE convScoped #-}
convScoped scope ctx envL envR (ScopedAST binderL bodyL) (Extend extend) (ScopedAST binderR bodyR)
  | not (Foil.unsafeUnifiablePatterns binderL binderR) = False
  | otherwise =
      Foil.withRefreshedPattern scope binderL $ \extendL binderL' scope' ->
        case (Foil.assertDistinct binderL, Foil.assertDistinct binderR) of
          (Foil.Distinct, Foil.Distinct) ->
            let ctx'  = extend scope binderL' scope' ctx
                fresh = map VVar (Foil.namesOfPattern binderL')
                envR' = Foil.addSubstPattern (Foil.sink envR) binderR fresh
            in convertibleUnder scope' ctx' (extendL envL) envR' bodyL bodyR

-- | Two terms are convertible under their environments: evaluate each under
-- its own environment, then compare with 'conv'. The function is @INLINE@,
-- so that a language's @SPECIALIZE@ pragmas for 'conv' and
-- 'FreeFoil.NbE.eval' apply to it. As @INLINABLE@, it would be specialised
-- only where the scope is fixed too.
convertibleUnder ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  AST binder sig i1 ->
  AST binder sig i2 ->
  Bool
{-# INLINE convertibleUnder #-}
convertibleUnder scope ctx envL envR t u =
  conv scope ctx (eval scope ctx envL t) (eval scope ctx envR u)

-- | Two terms are convertible: evaluate both, then compare with 'conv'.
convertible ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  ctx n ->
  AST binder sig n ->
  AST binder sig n ->
  Bool
{-# INLINABLE convertible #-}
convertible scope ctx = convertibleUnder scope ctx Foil.identitySubst Foil.identitySubst
