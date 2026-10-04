{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Data.List (isInfixOf)
import Data.Maybe (isJust)
import qualified Data.Map.Strict as Map
import System.Timeout (timeout)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import FreeFoil.NbE
  ( Distinct, Scope, S (VoidS), alphaEquiv, emptyScope, identitySubst
  , extendScope, nameId, nameOf, withFresh )
import LambdaPi
import LambdaPi.Parser (parseLambdaPi, parseOpen, resolve, withFreeVars)
import LambdaPi.PrettyPrint (ppValue, ppValueStruct)
import LambdaPi.Gen (Closed (..), OpenTerm (..), freeVars)
import qualified LambdaPi.LambdaNWays as LNW
import qualified LambdaPi.Monomorphic as Mono
import qualified Booleans as B
import qualified LambdaLet as LL
import qualified LambdaLet.Examples as LLE
import qualified LambdaLet.Parser as LLP

main :: IO ()
main =
  defaultMain $
    localOption (QuickCheckMaxSize 20) $
      testGroup "lambda-pi"
        [ betaTests
        , underBinderTests
        , piTests
        , piDepthTests
        , whnfTests
        , neutralTests
        , roundTripTests
        , valueTests
        , lambdaNWaysTests
        , booleansTests
        , lambdaLetTests
        , propertyTests
        ]

-- | Two closed terms are equal up to renaming (alpha-equivalence).
alphaEq :: LambdaPi VoidS -> LambdaPi VoidS -> Assertion
alphaEq a b = alphaEquiv emptyScope a b @?= True

-- | The reference normaliser and both NbE normalisers (the generic one and
-- the monomorphic baseline) reduce @term@ to something alpha-equivalent to
-- @expected@.
bothNormaliseTo :: TestName -> LambdaPi VoidS -> LambdaPi VoidS -> TestTree
bothNormaliseTo name term expected =
  testGroup name
    [ testCase "reference nf" (alphaEq (nf emptyScope term) expected)
    , testCase "nfNbe"        (alphaEq (nfNbe emptyScope term) expected)
    , testCase "nfMono"       (alphaEq (Mono.nfMono emptyScope term) expected)
    ]

-- Booleans: a second Eval instance, exercising the generic nfNbe on a
-- different signature and a non-application eliminator (if). -----------------

-- | A structural view of a Boolean normal form. These terms have no binders, so
-- ordinary equality (not alpha-equivalence) is the right notion.
data SB = SBTrue | SBFalse | SBIf SB SB SB | SBVar Int
  deriving (Eq, Show)

sb :: B.BoolTm n -> SB
sb = \case
  B.TT       -> SBTrue
  B.FF       -> SBFalse
  B.If c t f -> SBIf (sb c) (sb t) (sb f)
  Var x      -> SBVar (nameId x)
  _          -> error "sb: unexpected term"

booleansTests :: TestTree
booleansTests =
  testGroup "booleans (second Eval instance)"
    [ testCase "if true selects the then-branch" $
        sb (B.nf emptyScope (B.If B.TT B.TT B.FF)) @?= SBTrue
    , testCase "if false selects the else-branch" $
        sb (B.nf emptyScope (B.If B.FF B.TT B.FF)) @?= SBFalse
    , testCase "a reducible condition is evaluated first" $
        sb (B.nf emptyScope (B.If (B.If B.TT B.FF B.TT) B.TT B.FF)) @?= SBFalse
    , testCase "an if stuck on a neutral condition is preserved" $
        withFresh emptyScope $ \x ->
          let scope = extendScope x emptyScope
              term  = B.If (Var (nameOf x)) B.TT B.FF
           in sb (B.nf scope term) @?= SBIf (SBVar (nameId (nameOf x))) SBTrue SBFalse
    ]

-- Lambda-let: zoo series step 1 (let / definitions). An eliminator that
-- always fires: no let survives normalisation, and NbE gets it with one
-- 'evalSig' case and no framework change. ------------------------------------

-- | Alpha-equivalence for closed lambda-let terms.
llAlphaEq :: LL.LambdaLet VoidS -> LL.LambdaLet VoidS -> Assertion
llAlphaEq a b = alphaEquiv emptyScope a b @?= True

lambdaLetTests :: TestTree
lambdaLetTests =
  testGroup "lambda-let (zoo step 1: let / definitions)"
    [ testGroup "nfNbe agrees with reference nf on every example"
        [ testCase nm $
            alphaEquiv emptyScope (LL.nfNbe emptyScope t) (LL.nf emptyScope t) @?= True
        | (nm, t) <- LLE.examples
        ]
    , testCase "a let-bound definition is applied: letId is the identity" $
        llAlphaEq (LL.nfNbe emptyScope LLE.letId) "\\y. y"
    , testCase "definition used twice: letChurch is Church four" $
        llAlphaEq (LL.nfNbe emptyScope LLE.letChurch) "\\s. \\z. s (s (s (s z)))"
    , testCase "an inner let shadows the outer binding" $
        llAlphaEq (LL.nfNbe emptyScope LLE.letShadow) "\\b. b b"
    , testCase "whnfNbe reduces a top-level let (let is a head redex)" $
        llAlphaEq (LL.whnfNbe emptyScope "let i = \\x. x in i") "\\x. x"
    , testCase "whnfNbe leaves a let under a lambda untouched" $
        llAlphaEq (LL.whnfNbe emptyScope LLE.letUnderLam) LLE.letUnderLam
    , testCase "nfNbe, in contrast, reduces the let under the lambda" $
        llAlphaEq (LL.nfNbe emptyScope LLE.letUnderLam) "\\f. f f"
    , testCase "an unused divergent binding is never evaluated (call-by-need)" $
        llAlphaEq (LL.nfNbe emptyScope LLE.letUnused) "\\y. y"
    , testCase "a let bound to a neutral still reduces (open term)" $
        LLP.withFreeVars emptyScope Map.empty ["f"] $ \scope env ->
          case (,) <$> LLP.parseOpen scope env "let y = f in y y"
                   <*> LLP.parseOpen scope env "f f" of
            Left err            -> assertFailure ("parse failed: " ++ err)
            Right (t, expected) ->
              alphaEquiv scope (LL.nfNbe scope t) expected @?= True
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

-- Weak-head normal form. -----------------------------------------------------

-- | 'whnfNbe' reduces the head but stops at binders. It shares 'eval' with
-- 'nfNbe' and differs only in how far quoting is driven: a redex under a binder
-- survives 'whnfNbe' but is reduced by 'nfNbe'.
whnfTests :: TestTree
whnfTests =
  testGroup "whnfNbe (weak-head normal form)"
    [ testCase "reduces the head redex" $
        alphaEq (whnfNbe emptyScope "(\\x. x) (\\y. y)") "\\z. z"
    , testCase "leaves a redex under a lambda untouched" $
        alphaEq (whnfNbe emptyScope "\\f. (\\x. x) f") "\\f. (\\x. x) f"
    , testCase "nfNbe, in contrast, reduces under the lambda" $
        alphaEq (nfNbe emptyScope "\\f. (\\x. x) f") "\\g. g"
    , testCase "leaves a redex in a Pi codomain under a binder" $
        alphaEq (whnfNbe emptyScope "\\f. (a : f) -> (\\y. y) a")
                "\\f. (a : f) -> (\\y. y) a"
    ]

-- Deep Pi nesting must stay linear (regression for the exponential blow-up
-- where each nested codomain was normalised once by 'eval' and again by
-- 'quote'). At depth 100 a quadratic-or-worse normaliser would never finish;
-- the eager-values representation visits each subterm once, so this is instant.
piDepthTests :: TestTree
piDepthTests =
  testGroup "deep Pi nesting stays linear (regression)"
    [ testCase (name ++ " agrees with reference nf at depth " ++ show d) $
        case parseLambdaPi (deepPi d) of
          Left err -> assertFailure ("parse failed: " ++ err)
          Right t  -> alphaEq (normalise emptyScope t) (nf emptyScope t)
    | d <- [100 :: Int]
    , (name, normalise) <- [("nfNbe", nfNbe), ("nfMono", Mono.nfMono)]
    ]

-- | A chain of @n@ nested dependent function types
-- @(v0 : \\t. t) -> ... -> (v_{n-1} : \\t. t) -> \\w. w@, with distinct,
-- unused binders. There are no redexes in the types, so both normalisers do a
-- single linear pass — unless NbE re-normalises codomains, which is
-- exponential in @n@.
deepPi :: Int -> String
deepPi n =
  concatMap (\i -> "(v" ++ show i ++ " : \\t. t) -> ") [0 .. n - 1] ++ "\\w. w"

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
      ++ [ testCase (nm ++ ": monoNf agrees with reference nf") $
             LNW.aeq (LNW.monoNf t) (LNW.refNf t) @?= True
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
  testGroup "properties"
    [ testGroup "nfNbe agrees with reference nf"
        [ testProperty "closed terms" (propClosed nfNbe)
        , testProperty "open terms (neutrals)" (propOpen nfNbe)
        , testProperty "nfNbe . whnfNbe agrees with reference nf" propWhnf
        ]
    , testGroup "nfMono (monomorphic baseline) agrees with reference nf"
        [ testProperty "closed terms" (propClosed Mono.nfMono)
        , testProperty "open terms (neutrals)" (propOpen Mono.nfMono)
        ]
    ]

-- | A normaliser under test, polymorphic in the scope like 'nfNbe'.
type Normaliser = forall n. Distinct n => Scope n -> LambdaPi n -> LambdaPi n

propClosed :: Normaliser -> Closed -> Property
propClosed normalise (Closed t) = ioProperty (agrees normalise emptyScope t)

propOpen :: Normaliser -> OpenTerm -> Property
propOpen normalise (OpenTerm raw) =
  withFreeVars emptyScope Map.empty freeVars $ \scope env ->
    ioProperty (agrees normalise scope (resolve scope env raw))

-- | Weak-head normalising and then fully normalising yields the same normal
-- form as the reference @nf@: @whnfNbe@ reduces a prefix of the work @nfNbe@
-- does, so completing it must agree. (Same time-budget discipline as 'agrees'.)
propWhnf :: Closed -> Property
propWhnf (Closed t) = ioProperty (agrees' emptyScope t)
  where
    agrees' scope term = do
      let a = nf scope term
          b = nfNbe scope (whnfNbe scope term)
      nfDone  <- finished (evaluate (rnf a))
      nbeDone <- finished (evaluate (rnf b))
      pure $ case (nfDone, nbeDone) of
        (True, True)  -> counterexample "nfNbe . whnfNbe and nf disagree"
                           (property (alphaEquiv scope a b))
        (False, _)    -> property Discard
        (True, False) -> counterexample
          "nfNbe . whnfNbe did not finish within the budget though nf did"
          (property False)
    finished act = isJust <$> timeout 1000000 act

-- | An NbE normaliser and the reference normaliser produce alpha-equivalent
-- normal forms.
--
-- The untyped language admits non-normalising terms, so each normal form is
-- forced under a time budget. The two outcomes are compared rather than
-- silently discarded on any timeout: a case is discarded only when the
-- /reference/ 'nf' also fails to terminate (a genuinely divergent term). If
-- 'nf' finishes but the NbE normaliser does not, that is a real regression
-- (e.g. an exponential blow-up) and the property fails instead of hiding it.
agrees :: Distinct n => Normaliser -> Scope n -> LambdaPi n -> IO Property
agrees normalise scope t = do
  let a = nf scope t
      b = normalise scope t
  nfDone  <- finished (evaluate (rnf a))
  nbeDone <- finished (evaluate (rnf b))
  pure $ case (nfDone, nbeDone) of
    (True, True) ->
      counterexample "NbE and nf disagree" (property (alphaEquiv scope a b))
    (False, _) ->
      property Discard  -- reference diverged: nothing to compare against
    (True, False) ->
      counterexample
        "NbE did not finish within the budget though reference nf did"
        (property False)
  where
    finished act = isJust <$> timeout budgetMicros act
    budgetMicros = 1000000  -- 1 second
