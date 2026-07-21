{-# LANGUAGE DataKinds #-}

-- | QuickCheck generators for lambda-pi terms.
--
-- Terms are generated at the raw (named) level of "LambdaPi.Raw" while tracking
-- the set of in-scope variable names, which guarantees well-scopedness. A raw
-- term is then converted to scope-safe free-foil syntax with 'resolve' (the
-- generated conversion). Generating names positionally (@v0@, @v1@, ... by
-- binder depth) keeps binders on a single spine distinct while allowing
-- harmless reuse across disjoint branches.
module LambdaPi.Gen
  ( Closed (..)
  , OpenTerm (..)
  , freeVars
  , genTerm
  ) where

import qualified Data.Map.Strict as Map
import Test.QuickCheck

import FreeFoil.NbE (S (VoidS), emptyScope)
import LambdaPi (LambdaPi)
import LambdaPi.Parser (resolve)
import LambdaPi.Syntax.Abs (Term (..), Pattern (..), ScopedTerm (..), VarIdent (..))

-- | A random closed lambda-pi term.
newtype Closed = Closed (LambdaPi VoidS)

instance Show Closed where
  show (Closed t) = show t

instance Arbitrary Closed where
  arbitrary = Closed . resolve emptyScope Map.empty <$> sized (genTerm [])

-- | A random raw term over the fixed 'freeVars', for exercising open terms
-- (neutrals) once resolved in a scope holding those free variables.
newtype OpenTerm = OpenTerm Term
  deriving (Show)

instance Arbitrary OpenTerm where
  arbitrary = OpenTerm <$> sized (genTerm freeVars)

-- | Free variables available to the open-term generator.
freeVars :: [String]
freeVars = ["a", "b", "c"]

-- | Generate a raw term whose free variables are drawn from @vars@, with a size
-- budget. When @vars@ is empty (closed terms) the generator never emits a bare
-- variable, so it always produces a binder at the leaves.
genTerm :: [String] -> Int -> Gen Term
genTerm vars n
  | n <= 1 = leaf
  | otherwise =
      frequency $
        [ (3, App <$> genTerm vars half <*> genTerm vars half)
        , (3, genLam)
        , (2, genPi)
        ]
        ++ [ (4, var <$> elements vars) | not (null vars) ]
  where
    half = n `div` 2

    leaf
      | null vars = genLam
      | otherwise = oneof [var <$> elements vars, genLam]

    fresh = "v" ++ show (length vars)

    var x = Var (VarIdent x)
    scoped x body = (PatternVar (VarIdent x), AScopedTerm body)

    genLam = do
      body <- genTerm (fresh : vars) (n - 1)
      let (pat, sc) = scoped fresh body
      pure (Lam pat sc)
    genPi = do
      dom  <- genTerm vars half
      body <- genTerm (fresh : vars) half
      let (pat, sc) = scoped fresh body
      pure (Pi pat dom sc)
