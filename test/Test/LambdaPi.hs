{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
-- | Tests of lambda-pi: the generic 'nf' and 'whnf', the monomorphic
-- baseline 'Mono.nf', the reference normaliser, and conversion checking, on
-- examples and random terms.
module Test.LambdaPi (tests) where

import Control.DeepSeq (deepseq)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE.Conversion (convertible)
import LambdaPi
import LambdaPi.Parser (parseLambdaPi, parseOpen, resolve, withFreeVars)
import LambdaPi.PrettyPrint (ppValue, ppValueStruct)
import qualified LambdaPi.Monomorphic as Mono
import Test.Agree (agreesWithin)
import Test.LambdaPi.Gen (Closed (..), OpenTerm (..), freeVars)

tests :: TestTree
tests =
  testGroup "lambda-pi"
    [ betaTests
    , underBinderTests
    , piTests
    , piDepthTests
    , whnfTests
    , neutralTests
    , roundTripTests
    , valueTests
    , propertyTests
    , conversionTests
    ]

-- | Two closed terms are equal up to renaming (alpha-equivalence).
alphaEq :: LambdaPi VoidS -> LambdaPi VoidS -> Assertion
alphaEq a b = alphaEquiv emptyScope a b @?= True

-- | The reference normaliser and both NbE normalisers reduce @term@ to
-- something α-equivalent to @expected@.
bothNormaliseTo :: TestName -> LambdaPi VoidS -> LambdaPi VoidS -> TestTree
bothNormaliseTo name term expected =
  testGroup name
    [ testCase "nfSubst"      (alphaEq (nfSubst emptyScope term) expected)
    , testCase "nf"           (alphaEq (nf emptyScope term) expected)
    , testCase "Mono.nf"      (alphaEq (Mono.nf emptyScope term) expected)
    ]

-- Beta-reduction

betaTests :: TestTree
betaTests =
  testGroup "beta-reduction (closed)"
    [ bothNormaliseTo "identity applied to identity"
        "(\\x. x) (\\y. y)" "\\z. z"
    , bothNormaliseTo "K combinator drops its second argument"
        "(\\x. \\y. x) (\\a. a) (\\b. \\c. b)" "\\z. z"
    , bothNormaliseTo "Church 2 * 2 = 4"
        appTwoStr "\\s. \\z. s (s (s (s z)))"
    ]
  where
    -- Written as a string to double as a parser check; equals 'appTwo'.
    appTwoStr = "(\\s. \\z. s (s z)) (\\s. \\z. s (s z))"

-- Normalisation under binders

underBinderTests :: TestTree
underBinderTests =
  testGroup "normalisation under binders"
    [ bothNormaliseTo "redex reduced under a lambda"
        "\\f. (\\x. x) f" "\\g. g"
    , bothNormaliseTo "redex reduced under two lambdas"
        "\\f. \\y. (\\x. x) (f y)" "\\g. \\w. g w"
    , testCase "appTwo constant matches its string form" $
        alphaEq (nf emptyScope appTwo) "\\s. \\z. s (s (s (s z)))"
    ]

-- Pi

piTests :: TestTree
piTests =
  testGroup "Pi (dependent function types)"
    [ bothNormaliseTo "redex in the codomain is reduced"
        "(a : \\t. t) -> (\\y. y) a" "(a : \\t. t) -> a"
    , bothNormaliseTo "neutral codomain under a lambda is preserved"
        "\\f. (a : f) -> f a" "\\f. (a : f) -> f a"
    , bothNormaliseTo "non-dependent arrow (unused binder)"
        "(q : \\z. z) -> \\w. w" "(q : \\z. z) -> \\w. w"
    ]

-- Weak-head normal form

whnfTests :: TestTree
whnfTests =
  testGroup "whnf (weak-head normal form)"
    [ testCase "reduces the head redex" $
        alphaEq (whnf emptyScope "(\\x. x) (\\y. y)") "\\z. z"
    , testCase "leaves a redex under a lambda untouched" $
        alphaEq (whnf emptyScope "\\f. (\\x. x) f") "\\f. (\\x. x) f"
    , testCase "nf, in contrast, reduces under the lambda" $
        alphaEq (nf emptyScope "\\f. (\\x. x) f") "\\g. g"
    , testCase "leaves a redex in a Pi codomain under a binder" $
        alphaEq (whnf emptyScope "\\f. (a : f) -> (\\y. y) a")
                "\\f. (a : f) -> (\\y. y) a"
    ]

-- Deep Pi nesting stays linear: a regression test for the exponential blow-up
-- in which each codomain was normalised by eval and once more by quote.
piDepthTests :: TestTree
piDepthTests =
  testGroup "deep Pi nesting stays linear (regression)"
    [ testCase (name ++ " agrees with nfSubst at depth " ++ show d) $
        case parseLambdaPi (deepPi d) of
          Left err -> assertFailure ("parse failed: " ++ err)
          Right t  -> alphaEq (normalise emptyScope t) (nfSubst emptyScope t)
    | d <- [100 :: Int]
    , (name, normalise) <- [("nf", nf), ("Mono.nf", Mono.nf)]
    ]

-- | @n@ nested dependent function types with distinct, unused binders and no
-- redexes: @(v0 : \\t. t) -> ... -> (v_{n-1} : \\t. t) -> \\w. w@.
deepPi :: Int -> String
deepPi n =
  concatMap (\i -> "(v" ++ show i ++ " : \\t. t) -> ") [0 .. n - 1] ++ "\\w. w"

-- Neutrals

neutralTests :: TestTree
neutralTests =
  testGroup "neutrals with free variables"
    [ testCase "NbE preserves f ((\\x. x) g) as the neutral f g" $
        neutralExampleOk @?= True
    , testCase "NbE agrees with nfSubst on f ((\\x. x) g)" $
        openAgrees ["f", "g"] "f ((\\x. x) g)" @?= True
    , testCase "NbE agrees with nfSubst on a (\\y. b y) applied" $
        openAgrees ["a", "b"] "(\\x. a x) (b a)" @?= True
    ]

-- | Parse @s@ in a scope holding the named free variables; NbE and the
-- reference normaliser agree on it up to α.
openAgrees :: [String] -> String -> Bool
openAgrees names s =
  withFreeVars emptyScope Map.empty names $ \scope env ->
    case parseOpen scope env s of
      Left _  -> False
      Right t -> alphaEquiv scope (nf scope t) (nfSubst scope t)

-- Parser and printer

roundTripTests :: TestTree
roundTripTests =
  testGroup "parse . show round-trips"
    [ testCase (show t) (roundTrips t @?= True) | t <- roundTripExamples ]
  where
    roundTrips t = case parseLambdaPi (show t) of
      Right t' -> alphaEquiv emptyScope t t'
      Left _   -> False

roundTripExamples :: [LambdaPi VoidS]
roundTripExamples =
  [ "\\x. x"
  , "(\\x. x) (\\y. y)"
  , "\\f. \\x. f (f x)"
  , "\\f. \\g. \\x. f (g x) ((\\y. y) x)"
  , "(a : \\t. t) -> (\\y. y) a"
  , "\\f. (a : f) -> f a"
  , "(q : \\z. z) -> \\w. w"
  ]

-- Value inspection

valueTests :: TestTree
valueTests =
  testGroup "value inspection"
    [ testCase "structural Show of a lambda value mentions its suspended node" $
        assertBool ("got: " ++ s) ("lam" `isInfixOf` s)
    , testCase "Show on a value equals ppValueStruct" $
        show idVal @?= ppValueStruct idVal
    , testCase "ppValue quotes back to the identity" $
        assertBool ("got: " ++ ppValue emptyScope idVal)
          (either (const False) (alphaEquiv emptyScope "\\z. z")
             (parseLambdaPi (ppValue emptyScope idVal)))
    ]
  where
    idVal = eval emptyScope identitySubst ("\\x. x" :: LambdaPi VoidS)
    s = ppValueStruct idVal

-- Properties

propertyTests :: TestTree
propertyTests =
  testGroup "properties"
    [ testGroup "nf agrees with nfSubst"
        [ testProperty "closed terms" (propClosed nf)
        , testProperty "open terms (neutrals)" (propOpen nf)
        , testProperty "nf . whnf agrees with nfSubst" propWhnf
        ]
    , testGroup "Mono.nf (monomorphic baseline) agrees with nfSubst"
        [ testProperty "closed terms" (propClosed Mono.nf)
        , testProperty "open terms (neutrals)" (propOpen Mono.nf)
        ]
    ]

-- | A normaliser under test, polymorphic in the scope like 'nf'.
type Normaliser = forall n. Distinct n => Scope n -> LambdaPi n -> LambdaPi n

propClosed :: Normaliser -> Closed -> Property
propClosed normalise (Closed t) = ioProperty (agrees normalise emptyScope t)

propOpen :: Normaliser -> OpenTerm -> Property
propOpen normalise (OpenTerm raw) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    ioProperty (agrees normalise scope (resolve scope env raw))

-- | Fully normalising a weak-head normal form gives the reference normal
-- form.
propWhnf :: Closed -> Property
propWhnf (Closed t) =
  ioProperty $
    agreesWithin "nf . whnf" (alphaEquiv emptyScope)
      (nfSubst emptyScope t) (nf emptyScope (whnf emptyScope t))

-- | An NbE normaliser agrees with the reference normaliser up to α.
agrees :: Distinct n => Normaliser -> Scope n -> LambdaPi n -> IO Property
agrees normalise scope t =
  agreesWithin "NbE" (alphaEquiv scope) (nfSubst scope t) (normalise scope t)

-- Conversion checking

conversionTests :: TestTree
conversionTests =
  testGroup "conversion"
    [ testGroup "examples"
        [ convertibleAs True "a term and its normal form"
            "(\\s. \\z. s (s z)) (\\s. \\z. s (s z))" "\\s. \\z. s (s (s (s z)))"
        , convertibleAs True "bound variables are renamed"
            "\\x. \\y. x" "\\a. \\b. a"
        , convertibleAs True "redexes on both sides, under binders"
            "\\f. (\\x. x) f" "\\g. (\\y. \\z. z) g g"
        , convertibleAs True "Pi types compare domains and codomains"
            "(x : \\a. a) -> (\\y. y) x" "(z : (\\b. b) (\\c. c)) -> z"
        , convertibleAs False "different bound variables"
            "\\x. \\y. x" "\\x. \\y. y"
        , convertibleAs False "a lambda and a Pi type"
            "\\x. x" "(x : \\a. a) -> x"
        , convertibleAs False "a term without a normal form is told apart"
            "\\x. x" ("\\x. \\y. " ++ omega)
        , convertibleAs False "the first mismatch decides"
            ("\\x. \\y. x (" ++ omega ++ ")") ("\\x. \\y. y (" ++ omega ++ ")")
        ]
    , testGroup "properties"
        [ testProperty "a term is convertible with its normal form" propConvNf
        , testProperty "agrees with α-equivalence of normal forms" propConvPairs
        ]
    ]
  where
    omega = "(\\w. w w) (\\w. w w)"

convertibleAs :: Bool -> TestName -> String -> String -> TestTree
convertibleAs expected name t u =
  testCase name (convertible emptyScope (parseClosed t) (parseClosed u) @?= expected)
  where
    parseClosed = either error id . parseLambdaPi

-- | A term is convertible with its reference normal form, whenever that
-- exists within the budget.
propConvNf :: Closed -> Property
propConvNf (Closed t) =
  ioProperty $
    agreesWithin "convertible" (==)
      (normal `deepseq` True) (convertible emptyScope t normal)
  where
    normal = nfSubst emptyScope t

-- | Conversion agrees with comparing reference normal forms up to α. Most
-- random pairs differ, so this mainly checks the negative answers.
propConvPairs :: Closed -> Closed -> Property
propConvPairs (Closed t) (Closed u) =
  ioProperty $
    agreesWithin "convertible" (==)
      (alphaEquiv emptyScope (nfSubst emptyScope t) (nfSubst emptyScope u))
      (convertible emptyScope t u)
