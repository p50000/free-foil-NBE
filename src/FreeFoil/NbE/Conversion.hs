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
-- Glued values are compared as the context says
-- ('FreeFoil.NbE.glueSpeculation', 'FreeFoil.NbE.unfoldGlued'): their folded
-- sides first, as two
-- applications of one defined name to convertible arguments are
-- convertible, or their unfolded sides. This is the approximate conversion
-- checking of smalltt (Kovács, @unify@ in @src/Unification.hs@, and the
-- section "Approximate conversion checking" of its README), with the
-- strategy left to the context. "FreeFoil.NbE.Definitions" follows
-- smalltt's.
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

import           FreeFoil.NbE                (EtaScoped (..), EtaTerm (..), Eval (..), Extend (..), GlueSpeculation (..), Value, eval, refine)
import           FreeFoil.NbE.Internal.Value (Value' (..))

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
conv = convIn
  where
    -- Two values, refined first. The functions are local, so that a
    -- specialisation of 'conv' covers them. They close over nothing, so
    -- that no call allocates them.
    convIn :: Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool
    convIn scope ctx l r = sameHead Term scope ctx (refine scope ctx l) (refine scope ctx r)

    -- Two values compared without refining them: heads ('headsWith'), or
    -- values refined already. Their heads are compared the same way, every
    -- other position by 'convIn'.
    sameHead :: Foil.Distinct l => Position -> Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool
    sameHead pos scope' ctx' l' r' = case (l', r') of
      (VVar_ x, VVar_ y) -> x == y
      (VNode_ a, VNode_ b)
        | Just (All same) <- relateWith scope' ctx' (\v _ _ _ -> absurd v) (other scope') (heads scope') a b -> same
      -- The language pairs the positions of the two nodes, gives each
      -- scoped pair its extension of the context and each term pair its
      -- context.
      (VSuspended_ envL a, VSuspended_ envR b)
        | Just (All same) <- relateWith scope' ctx'
            (\x y ctx'' extend -> All (convScoped convIn scope' ctx'' envL envR x extend y))
            (other scope') (heads scope') a b -> same
      -- A glued value matches no node, so it is compared here, as the
      -- context says. Its sides are compared again as values of the same
      -- position: a term position by 'convIn', which refines them, a head
      -- as a head.
      (VGlued_ x foldedL unfoldedL, VGlued_ y foldedR unfoldedR) -> case glueSpeculation scope' ctx' x foldedL y foldedR of
        TryFolded ctxF ctxU ->
          again pos scope' ctxF foldedL foldedR
            || maybe False (\c -> again pos scope' c unfoldedL unfoldedR) ctxU
        CompareUnfolded ctxU -> again pos scope' ctxU unfoldedL unfoldedR
        Unrelated -> False
      (VGlued_ x _ unfoldedL, _) -> maybe False (\c -> again pos scope' c unfoldedL r') (unfoldGlued scope' ctx' x r')
      (_, VGlued_ y _ unfoldedR) -> maybe False (\c -> again pos scope' c l' unfoldedR) (unfoldGlued scope' ctx' y l')
      -- Nodes that do not match are compared by η. A node goes to 'VNode'
      -- exactly when it has no scoped subterms, so a 'VNode' and a
      -- 'VSuspended' never have the same constructor.
      _ -> convEta convIn scope' ctx' OnLeft l' r' || convEta convIn scope' ctx' OnRight r' l'

    -- The sides of glued values, compared again at their position.
    again :: Foil.Distinct l => Position -> Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool
    {-# INLINE again #-}
    again pos scope' ctx' a b = case pos of
      Term -> convIn scope' ctx' a b
      Head -> sameHead Head scope' ctx' a b

    -- A pair of term positions in its context: a head ('headsWith') or
    -- another position.
    heads, other :: Foil.Distinct l => Foil.Scope l -> Value binder sig l -> Value binder sig l -> ctx l -> All
    {-# INLINE heads #-}
    heads scope' a b ctx' = All (sameHead Head scope' ctx' a b)
    {-# INLINE other #-}
    other scope' a b ctx' = All (convIn scope' ctx' a b)

-- | Whether the values that 'conv' compares stand at a term position,
-- refined already, or at a head, which is not refined.
data Position = Term | Head

-- | The side of the comparison on which the introduction form of η stands.
data Side = OnLeft | OnRight

-- | One step of η: each position of an introduction form with an η law
-- against the other value observed at that position, on the side of the
-- introduction form, by the first function. 'False' for any other value.
convEta ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  (forall l. Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool) ->
  Foil.Scope n ->
  ctx n ->
  Side ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINE convEta #-}
convEta compare' scope ctx side intro other = case intro of
  VNode_ node ->
    maybe False (biall absurd id) (etaMatchWith (\v _ -> absurd v) observedTerm node)
  VSuspended_ env node ->
    maybe False biand (etaMatchWith ($) observedTerm (extendScopedWith (convObserved compare' scope ctx side env other) id node))
  VVar_ _ -> False
  VGlued_ {} -> False
  where
    observedTerm v (EtaTerm observe) = sides side (compare' scope ctx) v (observe scope ctx other)

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
  (forall l. Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool) ->
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
convObserved compare' scope ctx side env other (ScopedAST binder body) (Extend extend) (EtaScoped observe) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let ctx' = extend scope binder' scope' ctx
        in sides side (compare' scope' ctx')
             (eval scope' ctx' (extendEnv env) body)
             (observe scope' ctx' binder' (Foil.sink other))

-- | Compare two scoped subterms under their environments, by the first
-- function. The left binder is refreshed for the common scope and extends
-- the context as 'relateWith' says. When the two binders have the same
-- shape (they come from different scopes, so free-foil's
-- 'Foil.unsafeUnifiablePatterns' compares them), the names the left one
-- binds extend the right environment by position; otherwise the right
-- environment is extended with the right binder bound to the value the
-- left one stands for ('binderValue', 'bindValue'), so that a pair pattern
-- on one side and a variable on the other see the same value, the one as
-- its projections. A language whose binders stand for nothing leaves such
-- positions unrelated. Then the bodies are evaluated and compared.
convScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  (forall l. Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> Value binder sig l -> Bool) ->
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  ScopedAST binder sig i1 ->
  Extend ctx binder sig n ->
  ScopedAST binder sig i2 ->
  Bool
{-# INLINE convScoped #-}
convScoped compare' scope ctx envL envR (ScopedAST binderL bodyL) (Extend extend) (ScopedAST binderR bodyR) =
  Foil.withRefreshedPattern scope binderL $ \extendL binderL' scope' ->
    case (Foil.assertDistinct binderL, Foil.assertDistinct binderR) of
      (Foil.Distinct, Foil.Distinct) ->
        let ctx' = extend scope binderL' scope' ctx
            envR'
              | Foil.unsafeUnifiablePatterns binderL binderR =
                  Just (Foil.addSubstPattern (Foil.sink envR) binderR (map VVar_ (Foil.namesOfPattern binderL')))
              | otherwise =
                  bindValue scope' ctx' (Foil.sink envR) binderR =<< binderValue scope' ctx' binderL'
        in case envR' of
             Nothing -> False
             Just envR'' -> compare' scope' ctx' (eval scope' ctx' (extendL envL) bodyL) (eval scope' ctx' envR'' bodyR)

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
