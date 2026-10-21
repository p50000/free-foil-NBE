{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
-- | The monolithic language against the composed one: the two normalisers
-- agree on examples and on random terms, and the conversion between the two
-- syntaxes is the identity up to α.
module Test.Monolith (tests, genTerm) where

import qualified Data.Map.Strict        as Map
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil (alphaEquiv)

import qualified Fragments.Combined     as Composed
import qualified Monolith
import           Monolith.Parser        (resolve, withFreeVars)
import           Monolith.Syntax.Abs    (Pattern (..), ScopedTerm (..), Term (..), VarIdent (..))
import           Test.Agree             (agreesWithin)

tests :: TestTree
tests = testGroup "monolith against the composed language"
  [ testGroup "examples"
      [ normalisesTo "beta through a pair"
          "(\\x. (x, x)) zero" "(zero, zero)"
      , normalisesTo "a projection of a function's result"
          "fst ((\\x. (suc x, zero)) (suc (suc zero)))" "suc (suc (suc zero))"
      , normalisesTo "recursion on a computed numeral"
          "natrec ((\\x. x) (suc (suc zero))) { zero -> suc (suc (suc zero)) ; suc (k, r) -> suc r }"
          "suc (suc (suc (suc (suc zero))))"
      , normalisesTo "addition through split"
          "split (suc zero, suc (suc zero)) as (x, y) in natrec x { zero -> y ; suc (k, r) -> suc r }"
          "suc (suc (suc zero))"
      ]
  , testGroup "agree"
      [ testProperty "on closed terms" propClosed
      , testProperty "on open terms" propOpen
      ]
  , testProperty "the conversion between the syntaxes is the identity" propRoundTrip
  ]

normalisesTo :: TestName -> Monolith.Monolith VoidS -> Monolith.Monolith VoidS -> TestTree
normalisesTo name term expected = testGroup name
  [ testCase "monolith" $
      assertBool (show result) (alphaEquiv emptyScope result expected)
  , testCase "composed" $
      assertBool (show composed) (alphaEquiv emptyScope composed (Composed.fromMonolith expected))
  ]
  where
    result = Monolith.nf emptyScope term
    composed = Composed.nf emptyScope (Composed.fromMonolith term)

-- | The composed normaliser agrees with the monolithic one; terms contain
-- functions, so the comparison has the usual budget.
agree :: Distinct n => Scope n -> Monolith.Monolith n -> Property
agree scope t = ioProperty $
  agreesWithin "the composed nf" (alphaEquiv scope)
    (Composed.fromMonolith (Monolith.nf scope t))
    (Composed.nf scope (Composed.fromMonolith t))

propClosed :: ClosedTerm -> Property
propClosed (ClosedTerm raw) = agree emptyScope (resolve emptyScope Map.empty raw)

propOpen :: OpenTerm -> Property
propOpen (OpenTerm raw) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    agree scope (resolve scope env raw)

propRoundTrip :: OpenTerm -> Bool
propRoundTrip (OpenTerm raw) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    let t = resolve scope env raw
    in alphaEquiv scope (Composed.toMonolith (Composed.fromMonolith t)) t

-- * Generators

newtype ClosedTerm = ClosedTerm Term
  deriving (Show)

instance Arbitrary ClosedTerm where
  arbitrary = ClosedTerm <$> sized (genTerm [])

newtype OpenTerm = OpenTerm Term
  deriving (Show)

instance Arbitrary OpenTerm where
  arbitrary = OpenTerm <$> sized (genTerm freeVars)

freeVars :: [String]
freeVars = ["a", "b"]

-- | A random raw term over all three fragments, with free variables from
-- @vars@, within a size budget. Binder names are positional, so binders on
-- one spine are distinct; lambdas and Pi bind one name.
genTerm :: [String] -> Int -> Gen Term
genTerm vars n
  | n <= 1 = leaf
  | otherwise =
      frequency
        [ (3, App <$> sub <*> sub)
        , (3, Lam (PatternVar x) . AScopedTerm <$> genTerm (x' : vars) (n - 1))
        , (1, Pi (PatternVar x) <$> sub <*> (AScopedTerm <$> genTerm (x' : vars) half))
        , (2, Pair <$> sub <*> sub)
        , (1, Fst <$> sub)
        , (1, Snd <$> sub)
        , (2, Split <$> sub <*> pure (PatternPair x y) <*> (AScopedTerm <$> genTerm (y' : x' : vars) half))
        , (2, Suc <$> genTerm vars (n - 1))
        , (2, NatRec <$> sub <*> sub <*> pure (PatternPair x y) <*> (AScopedTerm <$> genTerm (y' : x' : vars) half))
        ]
  where
    leaf
      | null vars = oneof [pure Zero, pure (Lam (PatternVar (VarIdent "z")) (AScopedTerm (Var (VarIdent "z"))))]
      | otherwise = oneof [Var . VarIdent <$> elements vars, pure Zero]
    half = n `div` 2
    sub = genTerm vars half
    x' = "x" ++ show n
    y' = "y" ++ show n
    x = VarIdent x'
    y = VarIdent y'
