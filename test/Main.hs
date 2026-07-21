{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Control.Exception (evaluate)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import System.Timeout (timeout)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import FreeFoil.NbE (Distinct, Scope, S (VoidS), alphaEquiv, emptyScope, identitySubst)
import LambdaPi
import LambdaPi.Parser (parseLambdaPi, parseOpen, resolve, withFreeVars)
import LambdaPi.PrettyPrint (ppValue, ppValueStruct)
import LambdaPi.Gen (Closed (..), OpenTerm (..), freeVars)
import qualified LambdaPi.LambdaNWays as LNW

main :: IO ()
main =
  defaultMain $
    localOption (QuickCheckMaxSize 12) $
      testGroup "lambda-pi"
        [ betaTests
        , underBinderTests
        , piTests
        , neutralTests
        , roundTripTests
        , valueTests
        , lambdaNWaysTests
        , propertyTests
        ]

-- | Two closed terms are equal up to renaming (alpha-equivalence).
alphaEq :: LambdaPi VoidS -> LambdaPi VoidS -> Assertion
alphaEq a b = alphaEquiv emptyScope a b @?= True

-- | Both the reference normaliser and NbE reduce @term@ to something
-- alpha-equivalent to @expected@.
bothNormaliseTo :: TestName -> LambdaPi VoidS -> LambdaPi VoidS -> TestTree
bothNormaliseTo name term expected =
  testGroup name
    [ testCase "reference nf" (alphaEq (nf emptyScope term) expected)
    , testCase "nfNbe"        (alphaEq (nfNbe emptyScope term) expected)
    ]

-- Beta-reduction on closed terms. -------------------------------------------

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

-- Normalisation under binders. ----------------------------------------------

underBinderTests :: TestTree
underBinderTests =
  testGroup "normalisation under binders"
    [ bothNormaliseTo "redex reduced under a lambda"
        "\\f. (\\x. x) f" "\\g. g"
    , bothNormaliseTo "redex reduced under two lambdas"
        "\\f. \\y. (\\x. x) (f y)" "\\g. \\w. g w"
    , testCase "appTwo constant matches its string form" $
        alphaEq (nfNbe emptyScope appTwo) "\\s. \\z. s (s (s (s z)))"
    ]

-- Dependent function types. -------------------------------------------------

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

-- Neutrals with free variables. ---------------------------------------------

neutralTests :: TestTree
neutralTests =
  testGroup "neutrals with free variables"
    [ testCase "NbE preserves f ((\\x. x) g) as the neutral f g" $
        neutralNbeOk @?= True
    , testCase "NbE agrees with reference nf on f ((\\x. x) g)" $
        openAgrees ["f", "g"] "f ((\\x. x) g)" @?= True
    , testCase "NbE agrees with reference nf on a (\\y. b y) applied" $
        openAgrees ["a", "b"] "(\\x. a x) (b a)" @?= True
    ]

-- | Parse @s@ in a scope holding the named free variables, then check that NbE
-- and the reference normaliser agree up to alpha-equivalence.
openAgrees :: [String] -> String -> Bool
openAgrees names s =
  withFreeVars emptyScope Map.empty names $ \scope env ->
    case parseOpen scope env s of
      Left _  -> False
      Right t -> alphaEquiv scope (nfNbe scope t) (nf scope t)

-- Round-tripping (parser/printer regression). -------------------------------

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

-- Inspecting semantic values. ------------------------------------------------

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

-- lambda-n-ways adapter (untyped fragment). ----------------------------------

lambdaNWaysTests :: TestTree
lambdaNWaysTests =
  testGroup "lambda-n-ways adapter" $
    [ testCase (nm ++ ": nbeNf agrees with reference nf") $
        LNW.aeq (LNW.nbeNf t) (LNW.refNf t) @?= True
    | (nm, t) <- lcTerms
    ]
      ++ [ testCase (nm ++ ": toLC . fromLC round-trips") $
             LNW.aeq (LNW.toLC (LNW.fromLC t)) t @?= True
         | (nm, t) <- lcTerms
         ]

lcTerms :: [(String, LNW.LC LNW.IdInt)]
lcTerms =
  [ ("id", lam 0 (var 0))
  , ("K", lam 0 (lam 1 (var 0)))
  , ("id id", LNW.App (lam 0 (var 0)) (lam 1 (var 1)))
  , ("2*2", LNW.App church2 church2)
  ]
  where
    var i = LNW.Var (LNW.IdInt i)
    lam i b = LNW.Lam (LNW.IdInt i) b
    church2 = lam 0 (lam 1 (LNW.App (var 0) (LNW.App (var 0) (var 1))))

-- Properties. ---------------------------------------------------------------

propertyTests :: TestTree
propertyTests =
  testGroup "nfNbe agrees with reference nf"
    [ testProperty "closed terms" propClosed
    , testProperty "open terms (neutrals)" propOpen
    ]

propClosed :: Closed -> Property
propClosed (Closed t) = ioProperty (agrees emptyScope t)

propOpen :: OpenTerm -> Property
propOpen (OpenTerm raw) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    ioProperty (agrees scope (resolve scope env raw))

-- | NbE and the reference normaliser produce alpha-equivalent normal forms,
-- unless one fails to terminate within the time budget (in which case the case
-- is discarded — the untyped language admits non-normalising terms). Forcing
-- the 'alphaEquiv' result drives both normalisers far enough to decide.
agrees :: Distinct n => Scope n -> LambdaPi n -> IO Property
agrees scope t = do
  r <- timeout budgetMicros (evaluate (alphaEquiv scope (nfNbe scope t) (nf scope t)))
  pure (maybe (property Discard) property r)
  where
    budgetMicros = 1000000  -- 1 second
