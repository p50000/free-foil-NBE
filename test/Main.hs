module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Test.Booleans
import qualified Test.Definitions
import qualified Test.LambdaLet
import qualified Test.LambdaNWays
import qualified Test.LambdaPi
import qualified Test.Naturals
import qualified Test.Pairs

main :: IO ()
main =
  defaultMain $
    localOption (QuickCheckMaxSize 20) $
      testGroup "free-foil-nbe"
        [ Test.LambdaPi.tests
        , Test.Definitions.tests
        , Test.Booleans.tests
        , Test.LambdaLet.tests
        , Test.LambdaNWays.tests
        , Test.Naturals.tests
        , Test.Pairs.tests
        ]
