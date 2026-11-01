{-# LANGUAGE DataKinds #-}
-- | Tests of the dependent types language: every example elaborates and reaches its
-- normal form in a context of types, the conversion examples, the untyped
-- normal form without a context, and elaboration errors.
module Test.DependentTypes (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv)
import qualified FreeFoil.NbE as NbE

import DependentTypes (convertible, emptyTyping, nf)
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
    , testGroup "conversion in a context of types"
        [ testCase name $ do
            (t, _) <- elaborated t0 ty
            (u, _) <- elaborated u0 ty
            convertible emptyScope emptyTyping t u @?= expected
        | (name, Conversion ty t0 u0 expected) <- conversions
        ]
    , testCase "without a context a variable has no type" $ do
        let Example term0 ty _ = unitVariable
        (term, _) <- elaborated term0 ty
        let result = NbE.nf emptyScope NbE.NoContext term
        assertBool (show result) (alphaEquiv emptyScope result term)
    , testGroup "elaboration rejects"
        [ testCase "a term of another type" $
            rejects "\\(x : Unit). x" "(x : U) -> U"
        , testCase "an application of a non-function" $
            rejects "tt tt" "Unit"
        , testCase "a split of a value that is not of a Σ type" $
            rejects "\\(x : Unit). split x : Unit as (a, b) in a" "(x : Unit) -> Unit"
        ]
    ]
  where
    elaborated term ty = either assertFailure pure (elaborate term ty)
    rejects term ty = case elaborate term ty of
      Left _ -> pure ()
      Right (t, _) -> assertFailure ("elaborated to " ++ show t)
