{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
-- | Conversion checking: decide whether two values have the same normal form
-- up to renaming of bound variables and η, without reading them back.
--
-- This follows the conversion algorithm of Coquand, "An algorithm for
-- type-checking dependent types" (1996, §2.3.2 and Appendix A), with the
-- untyped η for surjective pairs of Abel and Coquand, "Untyped algorithmic
-- equality for Martin-Löf's logical framework with surjective pairs" (2007).
--
-- The check walks both values together and matches nodes with 'zipMatchWith2'
-- from free-foil, as free-foil's 'Control.Monad.Free.Foil.alphaEquiv' does
-- for terms. Under a binder it evaluates both bodies with the same fresh
-- names, but only when the comparison gets there, and it stops at the first
-- mismatch. So it can tell two terms apart even when one of them has no
-- normal form, and on convertible terms it does the work of normalisation
-- minus readback.
--
-- Two values of different shapes are compared by one-step η when either is
-- an introduction form with an η law ('FreeFoil.NbE.etaMatchWith'): each
-- position of that form against the other value observed at that position.
-- So @λx. f x@ against @f@ compares, under a fresh @x'@, the body @f x'@
-- with @f@ applied to @x'@, and @(fst p, snd p)@ against @p@ compares the
-- components with the projections of @p@.
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
import           Data.Bitraversable          (Bitraversable)
import           Data.Void                   (absurd)
import           Data.ZipMatchK              (ZipMatchK, zipMatchWith2)

import           FreeFoil.NbE                (EtaScoped (..), EtaTerm (..), Eval (..), Value (..), eval)

-- | Two values are convertible: their normal forms are equal up to renaming
-- of bound variables and η. Nodes match when they have the same constructor,
-- and then their subterms are compared left to right.
conv ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINABLE conv #-}
conv scope l r = case (l, r) of
  (VVar x, VVar y) -> x == y
  (VNode a, VNode b)
    | Just positions <- zipMatchWith2 (\v _ -> absurd v) (compared (conv scope)) a b ->
        biall absurd id positions
  (VSuspended envL a, VSuspended envR b)
    | Just positions <- zipMatchWith2 (compared (convScoped scope envL envR)) (compared (conv scope)) a b ->
        biand positions
  -- Nodes of different constructors are compared by η. A node goes to
  -- 'VNode' exactly when it has no scoped subterms, so a 'VNode' and a
  -- 'VSuspended' never have the same constructor.
  _ -> convEta scope l r || convEta scope r l
  where
    compared same x y = Just (same x y)

-- | One-step η: each position of an introduction form with an η law against
-- the other value observed at that position; 'False' for any other value.
convEta ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINABLE convEta #-}
convEta scope intro other = case intro of
  VNode node ->
    maybe False (biall absurd id) (etaMatchWith (\v _ -> absurd v) observedTerm node)
  VSuspended env node ->
    maybe False biand (etaMatchWith (convObserved scope env other) observedTerm node)
  VVar _ -> False
  where
    observedTerm v (EtaTerm observe) = conv scope v (observe scope other)

-- | A scoped position of an introduction form against the other value
-- observed under the position's refreshed binder.
convObserved ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  Value binder sig n ->
  ScopedAST binder sig i ->
  EtaScoped binder sig n ->
  Bool
{-# INLINABLE convObserved #-}
convObserved scope env other (ScopedAST binder body) (EtaScoped observe) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        conv scope'
          (eval scope' (extendEnv env) body)
          (observe scope' binder' (Foil.sink other))

-- | Compare two scoped subterms under their environments. Their binders must
-- have the same shape; they come from different scopes, so free-foil's
-- 'Foil.unsafeUnifiablePatterns' compares them. The left binder is refreshed
-- for the common scope, the names it binds extend both environments (the
-- right one by position in the pattern), and the bodies are compared with
-- 'convertibleUnder'.
convScoped ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  ScopedAST binder sig i1 ->
  ScopedAST binder sig i2 ->
  Bool
{-# INLINABLE convScoped #-}
convScoped scope envL envR (ScopedAST binderL bodyL) (ScopedAST binderR bodyR)
  | not (Foil.unsafeUnifiablePatterns binderL binderR) = False
  | otherwise =
      Foil.withRefreshedPattern scope binderL $ \extendL binderL' scope' ->
        case (Foil.assertDistinct binderL, Foil.assertDistinct binderR) of
          (Foil.Distinct, Foil.Distinct) ->
            let fresh = map VVar (Foil.namesOfPattern binderL')
                envR' = Foil.addSubstPattern (Foil.sink envR) binderR fresh
            in convertibleUnder scope' (extendL envL) envR' bodyL bodyR

-- | Two terms are convertible under their environments: evaluate each under
-- its own environment, then compare with 'conv'.
convertibleUnder ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  AST binder sig i1 ->
  AST binder sig i2 ->
  Bool
{-# INLINABLE convertibleUnder #-}
convertibleUnder scope envL envR t u =
  conv scope (eval scope envL t) (eval scope envR u)

-- | Two terms are convertible: evaluate both, then compare with 'conv'.
convertible ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n ->
  Bool
{-# INLINABLE convertible #-}
convertible scope = convertibleUnder scope Foil.identitySubst Foil.identitySubst
