{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE RankNTypes #-}
-- | Tests of naturals: the examples against their normal forms with both
-- normalisers, the weak-head normal form at a stuck recursion, arithmetic
-- by recursion against the numerals, and random terms, on which the generic
-- normaliser must agree with the reference one and conversion checking with
-- α-equivalence of normal forms. The language has no functions, so every
-- term normalises and no time budget is needed.
module Test.Naturals (tests) where

import qualified Data.Map.Strict as Map

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv)
import FreeFoil.NbE.Conversion (convertible)
import Naturals (Naturals, nf, nfSubst, numeral, whnf)
import Naturals.Examples
import Naturals.Parser (resolve, withFreeVars)
import Naturals.Syntax.Abs (Pattern (..), ScopedTerm (..), Term (..), VarIdent (..))

tests :: TestTree
tests =
  testGroup "naturals"
    [ testGroup "every example reaches its normal form"
        [ testGroup name
            [ testCase "nfSubst" (alphaEq emptyScope (nfSubst emptyScope term) normal)
            , testCase "nf"      (alphaEq emptyScope (nf emptyScope term) normal)
            ]
        | (name, term, normal) <- examples
        ]
    , testGroup "every open example reaches its normal form"
        [ withOpenExample ex $ \scope term normal ->
            testGroup name
              [ testCase "nfSubst" (alphaEq scope (nfSubst scope term) normal)
              , testCase "nf"      (alphaEq scope (nf scope term) normal)
              ]
        | (name, ex) <- openExamples
        ]
    , testGroup "whnf"
        [ testCase "reads a numeral back in full, as it has no scoped positions" $
            alphaEq emptyScope (whnf emptyScope plusTwoThree) (numeral 5)
        , withOpenExample redexUnderSucBranch $ \scope term _ ->
            testCase "leaves a redex under the two names of a stuck recursion" $
              alphaEq scope (whnf scope term) term
        , withOpenExample redexInZeroBranch $ \scope term normal ->
            testCase "reduces the zero branch of a stuck recursion, a term position" $
              alphaEq scope (whnf scope term) normal
        ]
    , testGroup "arithmetic by recursion"
        [ testProperty "plus" $ \(SmallNat m) (SmallNat n) ->
            alphaEquiv emptyScope (nf emptyScope (plusTerm m n)) (numeral (m + n))
        , testProperty "mult" $ \(SmallNat m) (SmallNat n) ->
            alphaEquiv emptyScope (nf emptyScope (multTerm m n)) (numeral (m * n))
        ]
    , testGroup "properties"
        [ testProperty "nf agrees with nfSubst on closed terms" propAgreesClosed
        , testProperty "nf agrees with nfSubst on open terms" propAgreesOpen
        , testProperty "a term is convertible with its normal form" propConvNf
        , testProperty "conversion agrees with α-equivalence of normal forms" propConvPairs
        ]
    ]

alphaEq :: Distinct n => Scope n -> Naturals n -> Naturals n -> Assertion
alphaEq scope a b = alphaEquiv scope a b @?= True

-- | A small natural number, for the arithmetic examples.
newtype SmallNat = SmallNat Int
  deriving (Show)

instance Arbitrary SmallNat where
  arbitrary = SmallNat <$> chooseInt (0, 6)

-- Properties on random terms

propAgreesClosed :: ClosedTerm -> Bool
propAgreesClosed (ClosedTerm raw) =
  let t = resolve emptyScope Map.empty raw
  in alphaEquiv emptyScope (nf emptyScope t) (nfSubst emptyScope t)

propAgreesOpen :: OpenTerm -> Bool
propAgreesOpen (OpenTerm raw) =
  withOpen raw $ \scope t -> alphaEquiv scope (nf scope t) (nfSubst scope t)

propConvNf :: OpenTerm -> Bool
propConvNf (OpenTerm raw) =
  withOpen raw $ \scope t -> convertible scope t (nfSubst scope t)

-- | Most random pairs differ, so this mainly checks the negative answers.
propConvPairs :: OpenTerm -> OpenTerm -> Bool
propConvPairs (OpenTerm rawT) (OpenTerm rawU) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    let t = resolve scope env rawT
        u = resolve scope env rawU
    in convertible scope t u == alphaEquiv scope (nfSubst scope t) (nfSubst scope u)

-- | Resolve a raw term over 'freeVars' and continue in its scope.
withOpen :: Term -> (forall n. Distinct n => Scope n -> Naturals n -> r) -> r
withOpen raw k =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    k scope (resolve scope env raw)

-- Generators

-- | A random closed raw term.
newtype ClosedTerm = ClosedTerm Term
  deriving (Show)

instance Arbitrary ClosedTerm where
  arbitrary = ClosedTerm <$> sized (genTerm [])

-- | A random raw term over the fixed 'freeVars'.
newtype OpenTerm = OpenTerm Term
  deriving (Show)

instance Arbitrary OpenTerm where
  arbitrary = OpenTerm <$> sized (genTerm freeVars)

-- | Free variables available to the open-term generator.
freeVars :: [String]
freeVars = ["a", "b", "c"]

-- | Generate a raw term with free variables from @vars@ within a size
-- budget. Binder names are positional, so binders on one spine are distinct.
genTerm :: [String] -> Int -> Gen Term
genTerm vars n
  | n <= 1 = leaf
  | otherwise =
      frequency $
        [ (3, Suc <$> genTerm vars (n - 1))
        , (3, genNatRec)
        , (1, pure Zero)
        ]
        ++ [ (2, var <$> elements vars) | not (null vars) ]
  where
    var x = Var (VarIdent x)
    leaf = oneof (pure Zero : [ var <$> elements vars | not (null vars) ])

    genNatRec = do
      scrutinee <- genTerm vars (n `div` 3)
      zeroCase  <- genTerm vars (n `div` 3)
      let k = "k" ++ show (length vars)
          r = "r" ++ show (length vars)
      step <- genTerm (r : k : vars) (n `div` 3)
      pure (NatRec scrutinee zeroCase (PatternRec (VarIdent k) (VarIdent r)) (AScopedTerm step))
