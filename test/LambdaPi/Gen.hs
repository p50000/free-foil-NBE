{-# LANGUAGE DataKinds #-}

-- | QuickCheck generators for lambda-pi terms. Terms are generated raw while
-- tracking the variables in scope, so they are well scoped, then converted
-- with 'resolve'. Binder names are positional (@v0@, @v1@, ... by depth), so
-- binders on one spine are distinct.
module LambdaPi.Gen
  ( Closed (..)
  , OpenTerm (..)
  , freeVars
  , genTerm
  ) where

import qualified Data.Map.Strict as Map
import Test.QuickCheck

import Control.Monad.Foil
import LambdaPi (LambdaPi)
import LambdaPi.Parser (resolve)
import LambdaPi.Syntax.Abs (Term (..), Pattern (..), ScopedTerm (..), VarIdent (..))

-- | A random closed lambda-pi term.
newtype Closed = Closed (LambdaPi VoidS)

instance Show Closed where
  show (Closed t) = show t

instance Arbitrary Closed where
  arbitrary = Closed . resolve emptyScope Map.empty <$> sized (genTerm [])

-- | A random raw term over the fixed 'freeVars', to be resolved in a scope
-- holding them.
newtype OpenTerm = OpenTerm Term
  deriving (Show)

instance Arbitrary OpenTerm where
  arbitrary = OpenTerm <$> sized (genTerm freeVars)

-- | Free variables available to the open-term generator.
freeVars :: [String]
freeVars = ["a", "b", "c"]

-- | Generate a raw term with free variables from @vars@ within a size budget;
-- with no variables available, leaves are lambdas.
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
