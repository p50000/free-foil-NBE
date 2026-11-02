{-# LANGUAGE DataKinds #-}
-- | Tests of the dependent types language: the normal forms, conversions and
-- subtypings of the examples in a context of types, and elaboration errors.
module Test.DependentTypes (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv)

import DependentTypes (convertible, emptyTyping, eval, fullyAnnotated, isSubtype, nf)
import DependentTypes.Elaborate (elaborate)
import DependentTypes.Examples

tests :: TestTree
tests =
  testGroup "dependent types"
    [ testGroup "every example reaches its normal form in a context of types"
        [ testCase name $ do
            (term, _) <- elaborated term0 ty
            (normal, _) <- elaborated normal0 ty
            let result = nf emptyScope emptyTyping term
            assertBool (show result) (alphaEquiv emptyScope result normal)
        | (name, Example term0 ty normal0) <- examples
        ]
    , testGroup "every node but a universe carries its type, before and after normalisation"
        [ testCase name $ do
            (term, _) <- elaborated term0 ty
            assertBool (show term) (fullyAnnotated term)
            let result = nf emptyScope emptyTyping term
            assertBool (show result) (fullyAnnotated result)
        | (name, Example term0 ty _) <- examples
        ]
    , testGroup "conversion in a context of types"
        [ testCase name $ do
            (t, _) <- elaborated t0 ty
            (u, _) <- elaborated u0 ty
            convertible emptyScope emptyTyping t u @?= expected
        | (name, Conversion ty t0 u0 expected) <- conversions
        ]
    , testGroup "subtyping in a context of types"
        [ testCase name $ do
            (a, _) <- elaborated a0 "U 3"
            (b, _) <- elaborated b0 "U 3"
            isSubtype emptyScope emptyTyping (evalType a) (evalType b) @?= expected
        | (name, Subtyping a0 b0 expected) <- subtypings
        ]
    , testGroup "elaboration rejects"
        [ testCase "a term of another type" $
            rejects "\\(x : Unit). x" "(x : U 0) -> U 0"
        , testCase "an application of a non-function" $
            rejects "tt tt" "Unit"
        , testCase "a projection of a value that is not of a Σ type" $
            rejects "\\(x : Unit). first x" "(x : Unit) -> Unit"
        , testCase "a universe in itself" $
            rejects "U 0" "U 0"
        , testCase "a type of a higher universe as one of a lower" $
            rejects "\\(A : U 1). A" "(A : U 1) -> U 0"
        , testCase "a function on a lower universe as one on a higher" $
            rejects "\\(f : (X : U 0) -> U 0). f" "(f : (X : U 0) -> U 0) -> (X : U 1) -> U 0"
        ]
    ]
  where
    elaborated term ty = either assertFailure pure (elaborate term ty)
    evalType = eval emptyScope emptyTyping identitySubst
    rejects term ty = case elaborate term ty of
      Left _ -> pure ()
      Right (t, _) -> assertFailure ("elaborated to " ++ show t)
