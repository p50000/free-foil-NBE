{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
-- | Conversion checking: decide whether two values have the same normal form
-- up to renaming of bound variables, without reading them back.
--
-- This follows the conversion algorithm of Coquand, "An algorithm for
-- type-checking dependent types" (1996, §2.3.2 and Appendix A).
--
-- The check walks both values together and matches nodes with 'zipMatchWithK'
-- from free-foil, as free-foil's 'Control.Monad.Free.Foil.alphaEquiv' does
-- for terms. Under a binder it evaluates both bodies with the same fresh
-- names, but only when the comparison gets there, and it stops at the first
-- mismatch. So it can tell two terms apart even when one of them has no
-- normal form, and on convertible terms it does the work of normalisation
-- minus readback.
--
-- Like the normaliser, the check is untyped and intensional: it decides β
-- and the language's own reductions, not η.
--
-- Two glued values are compared folded first: if the defined names and their
-- spines agree, the unfoldings agree, and nothing is unfolded. Otherwise, or
-- when only one side is glued, the comparison continues on the unfolded
-- sides. This is the folded-first unfolding of Kovács's smalltt.
module FreeFoil.NbE.Conversion
  ( conv
  , convertible
  , convertibleUnder
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (unsafeUnifiablePatterns)
import           Control.Monad.Free.Foil     (AST, ScopedAST (..))
import           Data.Maybe                  (isJust)
import           Data.Void                   (absurd)
import           Data.ZipMatchK              (Mappings (..), ZipMatchK (..))

import           FreeFoil.NbE                (Eval, Value, eval)
import           FreeFoil.NbE.Internal.Value (Value' (..))

-- | Two values are convertible: their normal forms are equal up to renaming
-- of bound variables. Nodes match when they have the same constructor, and
-- then their subterms are compared left to right.
conv ::
  (Eval binder sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINABLE conv #-}
conv scope = \cases
  (VGlued_ fl ul) (VGlued_ fr ur) -> conv scope fl fr || conv scope ul ur
  (VGlued_ _ ul) r -> conv scope ul r
  l (VGlued_ _ ur) -> conv scope l ur
  (VVar_ x) (VVar_ y) -> x == y
  (VNode_ l) (VNode_ r) ->
    matches (zipMatchWithK ((\v _ -> absurd v) :^: check (conv scope) :^: M0) l r)
  (VSuspended_ envL l) (VSuspended_ envR r) ->
    matches (zipMatchWithK (check (convScoped scope envL envR) :^: check (conv scope) :^: M0) l r)
  -- A node goes to 'VNode_' exactly when it has no scoped subterms, so a
  -- 'VNode_' and a 'VSuspended_' never have the same constructor.
  _ _ -> False
  where
    matches = isJust
    check same x y = if same x y then Just () else Nothing

-- | Compare two scoped subterms under their environments. Their binders must
-- have the same shape; they come from different scopes, so free-foil's
-- 'Foil.unsafeUnifiablePatterns' compares them. The left binder is refreshed
-- for the common scope, the names it binds extend both environments (the
-- right one by position in the pattern), and the bodies are compared with
-- 'convertibleUnder'.
convScoped ::
  (Eval binder sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
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
            let fresh = map VVar_ (Foil.namesOfPattern binderL')
                envR' = Foil.addSubstPattern (Foil.sink envR) binderR fresh
            in convertibleUnder scope' (extendL envL) envR' bodyL bodyR

-- | Two terms are convertible under their environments: evaluate each under
-- its own environment, then compare with 'conv'.
convertibleUnder ::
  (Eval binder sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
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
  (Eval binder sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n ->
  Bool
{-# INLINABLE convertible #-}
convertible scope = convertibleUnder scope Foil.identitySubst Foil.identitySubst
