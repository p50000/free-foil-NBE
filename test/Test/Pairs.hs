{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE RankNTypes #-}
-- | Tests of pairs: the examples against their normal forms with both
-- normalisers, the weak-head normal form at a two-name binder, and random
-- open terms, on which the generic normaliser must agree with the reference
-- one and conversion checking with α-equivalence of normal forms. The
-- language has no functions, so every term normalises and no time budget
-- is needed.
module Test.Pairs (tests) where

import qualified Data.Map.Strict as Map

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv)
import FreeFoil.NbE.Conversion (convertible)
import Pairs (Pairs, nf, nfSubst, whnf)
import Pairs.Examples
import Pairs.Parser (resolve, withFreeVars)
import Pairs.Syntax.Abs (Pattern (..), ScopedTerm (..), Term (..), VarIdent (..))

tests :: TestTree
tests =
  testGroup "pairs"
    [ testGroup "every example reaches its normal form"
        [ withOpenExample ex $ \scope term normal ->
            testGroup name
              [ testCase "nfSubst" (alphaEq scope (nfSubst scope term) normal)
              , testCase "nf"      (alphaEq scope (nf scope term) normal)
              ]
        | (name, ex) <- examples
        ]
    , testGroup "whnf"
        [ withOpenExample swap $ \scope term normal ->
            testCase "reduces a head split" (alphaEq scope (whnf scope term) normal)
        , withOpenExample redexUnderSplit $ \scope term _ ->
            testCase "leaves a redex under the two names of a stuck split" $
              alphaEq scope (whnf scope term) term
        ]
    , testGroup "properties"
        [ testProperty "nf agrees with nfSubst" propAgrees
        , testProperty "a term is convertible with its normal form" propConvNf
        , testProperty "conversion agrees with α-equivalence of normal forms" propConvPairs
        ]
    ]

alphaEq :: Distinct n => Scope n -> Pairs n -> Pairs n -> Assertion
alphaEq scope a b = alphaEquiv scope a b @?= True

-- Properties on random open terms

propAgrees :: OpenTerm -> Property
propAgrees (OpenTerm raw) =
  withOpen raw $ \scope t ->
    property (alphaEquiv scope (nf scope t) (nfSubst scope t))

propConvNf :: OpenTerm -> Property
propConvNf (OpenTerm raw) =
  withOpen raw $ \scope t ->
    property (convertible scope t (nfSubst scope t))

-- | Most random pairs differ, so this mainly checks the negative answers.
propConvPairs :: OpenTerm -> OpenTerm -> Property
propConvPairs (OpenTerm rawT) (OpenTerm rawU) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    let t = resolve scope env rawT
        u = resolve scope env rawU
    in property $
         convertible scope t u
           == alphaEquiv scope (nfSubst scope t) (nfSubst scope u)

-- | Resolve a raw term over 'freeVars' and continue in its scope.
withOpen :: Term -> (forall n. Distinct n => Scope n -> Pairs n -> r) -> r
withOpen raw k =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    k scope (resolve scope env raw)

-- Generator

-- | A random raw term over the fixed 'freeVars'.
newtype OpenTerm = OpenTerm Term
  deriving (Show)

instance Arbitrary OpenTerm where
  arbitrary = OpenTerm <$> sized (genTerm freeVars)

-- | Free variables available to the generator.
freeVars :: [String]
freeVars = ["a", "b", "c"]

-- | Generate a raw term with free variables from @vars@ within a size
-- budget. Binder names are positional, so binders on one spine are distinct.
genTerm :: [String] -> Int -> Gen Term
genTerm vars n
  | n <= 1 = var <$> elements vars
  | otherwise =
      frequency
        [ (3, Pair <$> half <*> half)
        , (2, Fst <$> genTerm vars (n - 1))
        , (2, Snd <$> genTerm vars (n - 1))
        , (3, genSplit)
        , (2, var <$> elements vars)
        ]
  where
    half = genTerm vars (n `div` 2)
    var x = Var (VarIdent x)

    genSplit = do
      scrutinee <- half
      let x = "x" ++ show (length vars)
          y = "y" ++ show (length vars)
      body <- genTerm (y : x : vars) (n `div` 2)
      pure (Split scrutinee (PatternPair (VarIdent x) (VarIdent y)) (AScopedTerm body))
