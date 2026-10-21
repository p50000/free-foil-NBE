{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
-- | The language composed from fragments: examples on mixed terms, agreement
-- with the standalone languages on embedded terms, properties on random mixed
-- terms, and the shape check of binders in conversion, which only a pattern
-- type with two constructors reaches. Terms are written in the syntax of the
-- monolithic language, through which the composed one parses.
module Test.Fragments
  ( tests
  , Mixed (..)
  , parseIn
  , resolve
  , natural
  , withFree
  , budgeted
  ) where

import           Control.DeepSeq           (NFData, rnf)
import           Control.Exception         (evaluate)
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import           System.Timeout            (timeout)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil   (alphaEquiv)
import           FreeFoil.NbE.Conversion   (convertible)

import           Fragments.Combined
import qualified LambdaPi
import qualified Monolith.Parser
import           Monolith.Syntax.Abs       (Term)
import qualified Naturals
import qualified Naturals.Parser
import qualified Pairs
import qualified Pairs.Parser
import           Test.Agree                (agreesWithin)
import           Test.LambdaPi.Gen         (Closed (..))
import           Test.Monolith             (genTerm)
import qualified Test.Naturals             as Naturals
import qualified Test.Pairs                as Pairs

tests :: TestTree
tests = testGroup "fragments"
  [ testGroup "examples"
      [ testGroup "closed terms" [ example name t expected | (name, t, expected) <- closedExamples ]
      , testGroup "open terms" [ openExample name t expected | (name, t, expected) <- openExamples ]
      , testGroup "whnf"
          [ openWhnf "keeps a redex under a stuck split"
              "split a as (x, y) in (\\z. z) x"
              "split a as (x, y) in (\\z. z) x"
          , openWhnf "reduces the zero branch of a stuck recursion, not the suc branch"
              "natrec a { zero -> (\\z. z) zero ; suc (k, r) -> (\\z. z) r }"
              "natrec a { zero -> zero ; suc (k, r) -> (\\z. z) r }"
          ]
      ]
  , testGroup "agrees with the standalone language"
      [ testProperty "lambda-pi, closed terms" propLambdaPi
      , testProperty "pairs, open terms" propPairs
      , testProperty "naturals, closed terms" propNaturalsClosed
      , testProperty "naturals, open terms" propNaturalsOpen
      ]
  , testGroup "mixed terms"
      [ testProperty "nf is idempotent" propIdempotent
      , testProperty "a term is convertible with its normal form" propConvertibleNf
      , testProperty "conversion agrees with alpha-equivalence of normal forms" propConversion
      ]
  , testGroup "binders of different shapes"
      [ testCase "are not convertible" $ do
          assertBool "one name against two" (not (convertible emptyScope oneName twoNames))
          assertBool "two names against one" (not (convertible emptyScope twoNames oneName))
      , testCase "are not alpha-equivalent" $
          assertBool "alphaEquiv" (not (alphaEquiv emptyScope oneName twoNames))
      , testCase "read back as they are" $
          assertBool "nf" (alphaEquiv emptyScope (nf emptyScope twoNames) twoNames)
      ]
  ]

-- * Terms, in the monolithic language's syntax

-- | A term of the composed language, parsed in a scope with named free
-- variables.
parseIn :: Distinct n => Scope n -> Map String (Name n) -> String -> Combined n
parseIn scope env = either (error . ("Test.Fragments: " ++)) fromMonolith . Monolith.Parser.parseOpen scope env

-- | A raw term of the monolithic language, resolved into the composed one.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Combined n
resolve scope env = fromMonolith . Monolith.Parser.resolve scope env

-- | The numeral @k@.
natural :: Int -> String
natural 0 = "zero"
natural k = "suc (" ++ natural (k - 1) ++ ")"

-- | Free variables of the open examples and the random mixed terms.
freeVars :: [String]
freeVars = ["a", "b"]

withFree :: (forall n. Distinct n => Scope n -> Map String (Name n) -> r) -> r
withFree = Monolith.Parser.withFreeVars emptyScope Map.empty freeVars

-- * Examples

closedExamples :: [(String, String, String)]
closedExamples =
  [ ( "beta through a pair"
    , "(\\x. (x, x)) zero"
    , "(zero, zero)" )
  , ( "a projection of a function's result"
    , "fst ((\\x. (suc x, zero)) (" ++ natural 2 ++ "))"
    , natural 3 )
  , ( "recursion on a computed numeral"
    , "natrec ((\\x. x) (" ++ natural 2 ++ ")) { zero -> " ++ natural 3 ++ " ; suc (k, r) -> suc r }"
    , natural 5 )
  , ( "addition through split"
    , "split (" ++ natural 1 ++ ", " ++ natural 2 ++ ") as (x, y) in natrec x { zero -> y ; suc (k, r) -> suc r }"
    , natural 3 )
  , ( "a function under natrec"
    , "natrec (" ++ natural 2 ++ ") { zero -> \\f. f ; suc (k, r) -> (\\g. g) r }"
    , "\\f. f" )
  ]

openExamples :: [(String, String, String)]
openExamples =
  [ ( "a stuck projection"
    , "fst (a zero)"
    , "fst (a zero)" )
  , ( "beta under a stuck split"
    , "split a as (x, y) in (\\z. z) x"
    , "split a as (x, y) in x" )
  , ( "a stuck recursion with normal branches"
    , "natrec a { zero -> (\\z. z) zero ; suc (k, r) -> (\\z. z) r }"
    , "natrec a { zero -> zero ; suc (k, r) -> r }" )
  , ( "split of a pair of neutrals"
    , "split (a, b) as (x, y) in (y, x)"
    , "(b, a)" )
  ]

example :: String -> String -> String -> TestTree
example name t expected = testCase name $
  let term = parseIn emptyScope Map.empty t
  in assertBool (show (nf emptyScope term)) (alphaEquiv emptyScope (nf emptyScope term) (parseIn emptyScope Map.empty expected))

openExample :: String -> String -> String -> TestTree
openExample name t expected = testCase name $ withFree $ \scope env ->
  let term = parseIn scope env t
  in assertBool (show (nf scope term)) (alphaEquiv scope (nf scope term) (parseIn scope env expected))

openWhnf :: String -> String -> String -> TestTree
openWhnf name t expected = testCase name $ withFree $ \scope env ->
  let term = parseIn scope env t
  in assertBool (show (whnf scope term)) (alphaEquiv scope (whnf scope term) (parseIn scope env expected))

-- * Agreement with the standalone languages on embedded terms

fromLambdaPi :: LambdaPi.LambdaPi n -> Combined n
fromLambdaPi = \case
  LambdaPi.Var x -> Var x
  LambdaPi.App f a -> App (fromLambdaPi f) (fromLambdaPi a)
  LambdaPi.Lam b body -> Lam (PatVar b) (fromLambdaPi body)
  LambdaPi.Pi dom b cod -> Pi (fromLambdaPi dom) (PatVar b) (fromLambdaPi cod)

fromPairs :: Pairs.Pairs n -> Combined n
fromPairs = \case
  Pairs.Var x -> Var x
  Pairs.Pair a b -> Pair (fromPairs a) (fromPairs b)
  Pairs.Fst p -> Fst (fromPairs p)
  Pairs.Snd p -> Snd (fromPairs p)
  Pairs.Split p x y body -> Split (fromPairs p) (PatPair x y) (fromPairs body)

fromNaturals :: Naturals.Naturals n -> Combined n
fromNaturals = \case
  Naturals.Var x -> Var x
  Naturals.Zero -> Zero
  Naturals.Suc t -> Suc (fromNaturals t)
  Naturals.NatRec n z k r s -> NatRec (fromNaturals n) (fromNaturals z) (PatPair k r) (fromNaturals s)

-- | Lambda-pi terms may diverge, so the comparison has the usual budget.
propLambdaPi :: Closed -> Property
propLambdaPi (Closed t) = ioProperty $
  agreesWithin "the composed nf" (alphaEquiv emptyScope)
    (fromLambdaPi (LambdaPi.nf emptyScope t))
    (nf emptyScope (fromLambdaPi t))

propPairs :: Pairs.OpenTerm -> Bool
propPairs (Pairs.OpenTerm raw) =
  Pairs.Parser.withFreeVars emptyScope Map.empty Pairs.freeVars $ \scope env ->
    let t = Pairs.Parser.resolve scope env raw
    in alphaEquiv scope (fromPairs (Pairs.nf scope t)) (nf scope (fromPairs t))

propNaturalsClosed :: Naturals.ClosedTerm -> Bool
propNaturalsClosed (Naturals.ClosedTerm raw) =
  let t = Naturals.Parser.resolve emptyScope Map.empty raw
  in alphaEquiv emptyScope (fromNaturals (Naturals.nf emptyScope t)) (nf emptyScope (fromNaturals t))

propNaturalsOpen :: Naturals.OpenTerm -> Bool
propNaturalsOpen (Naturals.OpenTerm raw) =
  Naturals.Parser.withFreeVars emptyScope Map.empty Naturals.freeVars $ \scope env ->
    let t = Naturals.Parser.resolve scope env raw
    in alphaEquiv scope (fromNaturals (Naturals.nf scope t)) (nf scope (fromNaturals t))

-- * Random mixed terms

newtype Mixed = Mixed Term
  deriving (Show)

instance Arbitrary Mixed where
  arbitrary = Mixed <$> sized (genTerm freeVars)

-- | Mixed terms contain functions, so a normal form may not exist: a case is
-- discarded when forcing @x@ does not finish within one second.
budgeted :: NFData a => a -> (a -> Bool) -> IO Property
budgeted x check = do
  done <- timeout 1000000 (evaluate (rnf x))
  pure $ case done of
    Nothing -> property Discard
    Just () -> property (check x)

propIdempotent :: Mixed -> Property
propIdempotent (Mixed raw) = withFree $ \scope env ->
  let v = nf scope (resolve scope env raw)
  in ioProperty $ budgeted v $ \v' -> alphaEquiv scope v' (nf scope v')

propConvertibleNf :: Mixed -> Property
propConvertibleNf (Mixed raw) = withFree $ \scope env ->
  let t = resolve scope env raw
  in ioProperty $ budgeted (nf scope t) $ \v -> convertible scope t v

propConversion :: Mixed -> Mixed -> Property
propConversion (Mixed raw1) (Mixed raw2) = withFree $ \scope env ->
  let t1 = resolve scope env raw1
      t2 = resolve scope env raw2
  in ioProperty $ budgeted (nf scope t1, nf scope t2) $ \(v1, v2) ->
       convertible scope t1 t2 == alphaEquiv scope v1 v2

-- * Binders of different shapes

oneName :: Combined VoidS
oneName = "\\x. x"

twoNames :: Combined VoidS
twoNames = "\\(x, y). x"
