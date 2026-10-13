{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Conversion checking: decide whether two values have the same normal form
-- up to renaming of bound variables, without reading them back.
--
-- This follows the conversion algorithm of Coquand, "An algorithm for
-- type-checking dependent types" (1996, §2.3.2 and Appendix A).
--
-- The check walks both values together and matches nodes with 'zipMatchWith2'
-- from free-foil, as free-foil's 'Control.Monad.Free.Foil.alphaEquiv' does
-- for terms. Under a binder it evaluates both bodies with the same fresh
-- names, but only when the comparison gets there, and it stops at the first
-- mismatch. So it can tell two terms apart even when one of them has no
-- normal form, and on convertible terms it does the work of normalisation
-- minus readback.
--
-- Like the normaliser, the check is untyped and intensional: it decides β
-- and the language's own reductions, not η.
module FreeFoil.NbE.Conversion
  ( conv
  , convertible
  ) where

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (AST, ScopedAST (..))
import           Data.Bitraversable      (Bitraversable)
import           Data.Maybe              (isJust)
import           Data.Void               (absurd)
import           Data.ZipMatchK          (ZipMatchK, zipMatchWith2)

import           FreeFoil.NbE            (Eval, Value (..), eval)

-- | Two values are convertible: their normal forms are equal up to renaming
-- of bound variables. Nodes match when they have the same constructor, and
-- then their subterms are compared left to right.
conv ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  Value binder sig n ->
  Bool
{-# INLINABLE conv #-}
conv scope = \cases
  (VVar x) (VVar y) -> x == y
  (VNode l) (VNode r) ->
    matches (zipMatchWith2 (\v _ -> absurd v) (check (conv scope)) l r)
  (VSuspended envL l) (VSuspended envR r) ->
    matches (zipMatchWith2 (check (convScoped scope envL envR)) (check (conv scope)) l r)
  -- A node goes to 'VNode' exactly when it has no scoped subterms, so a
  -- 'VNode' and a 'VSuspended' never have the same constructor.
  _ _ -> False
  where
    matches = isJust
    check same x y = if same x y then Just () else Nothing

-- | Compare two scoped subterms under their environments. Their binders must
-- have the same shape. The left binder is refreshed for the common scope, the
-- names it binds extend both environments (the right one by position in the
-- pattern), and the bodies are evaluated and compared.
convScoped ::
  forall binder sig n i1 i2.
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.Distinct i1, Foil.Distinct i2, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i1 n ->
  Foil.Substitution (Value binder sig) i2 n ->
  ScopedAST binder sig i1 ->
  ScopedAST binder sig i2 ->
  Bool
{-# INLINABLE convScoped #-}
convScoped scope envL envR (ScopedAST binderL bodyL) (ScopedAST binderR bodyR) =
  Foil.withRefreshedPattern scope binderL $ \extendL binderL' scope' ->
    sameShape binderL' $
      case (Foil.assertDistinct binderL, Foil.assertDistinct binderR) of
        (Foil.Distinct, Foil.Distinct) ->
          let fresh = map VVar (Foil.namesOfPattern binderL')
              envL' = extendL envL
              envR' = Foil.addSubstPattern (Foil.sink envR) binderR fresh
          in conv scope' (eval scope' envL' bodyL) (eval scope' envR' bodyR)
  where
    -- Refresh the right binder for the same scope too, so that the two
    -- patterns can be unified there; only the verdict is used.
    sameShape :: binder n l -> Bool -> Bool
    sameShape binderL' k =
      Foil.withRefreshedPattern scope binderR $
        \(_ :: Foil.Substitution (Value binder sig) i2 n -> Foil.Substitution (Value binder sig) l2 o) binderR' _ ->
        case Foil.unifyPatterns binderL' binderR' of
          Foil.NotUnifiable -> False
          _                 -> k

-- | Two terms are convertible: evaluate both, then compare with 'conv'.
convertible ::
  (Eval binder sig, Bitraversable sig, ZipMatchK sig, Foil.Distinct n, Foil.UnifiablePattern binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n ->
  Bool
{-# INLINABLE convertible #-}
convertible scope t u =
  conv scope (eval scope Foil.identitySubst t) (eval scope Foil.identitySubst u)
