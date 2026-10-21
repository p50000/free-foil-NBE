{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Transformations of free-foil syntax from one signature to another: a
-- bottom-up fold whose algebra may return any term, and the natural
-- transformation of signatures it specialises to, named after @hoistFree@
-- of the free package. Candidates for free-foil itself.
module FreeFoil.NbE.Transform
  ( foldAST
  , hoistAST
  ) where

import Control.Monad.Free.Foil (AST (..), ScopedAST (..))
import Data.Bifunctor          (Bifunctor (..))

-- | Rebuild a term bottom-up: every node is mapped over its subterms' results
-- and handed to the algebra, which returns the term that replaces it, and
-- every binder is mapped. The scope indices stay as they are.
foldAST ::
  forall binder1 binder2 sig1 sig2 n. Bifunctor sig1 =>
  (forall m. sig1 (ScopedAST binder2 sig2 m) (AST binder2 sig2 m) -> AST binder2 sig2 m) ->
  (forall i j. binder1 i j -> binder2 i j) ->
  AST binder1 sig1 n ->
  AST binder2 sig2 n
foldAST alg onBinder = go
  where
    go :: forall m. AST binder1 sig1 m -> AST binder2 sig2 m
    go (Var x)     = Var x
    go (Node node) = alg (bimap scoped go node)

    scoped :: forall m. ScopedAST binder1 sig1 m -> ScopedAST binder2 sig2 m
    scoped (ScopedAST binder body) = ScopedAST (onBinder binder) (go body)

-- | Change the signature of a term by a natural transformation of
-- signatures, keeping the binders.
hoistAST ::
  Bifunctor sig1 =>
  (forall a b. sig1 a b -> sig2 a b) ->
  AST binder sig1 n ->
  AST binder sig2 n
hoistAST f = foldAST (Node . f) id
