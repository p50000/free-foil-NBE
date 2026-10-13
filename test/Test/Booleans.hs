-- | Tests of Booleans: @if@ on constants and on a neutral condition. The
-- language has no reference normaliser, so the examples are checked against
-- their stated normal forms only.
module Test.Booleans (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Booleans (nf)
import Booleans.Examples

tests :: TestTree
tests =
  testGroup "booleans"
    [ testGroup "every example reaches its normal form"
        [ testCase name (alphaEquiv emptyScope (nf emptyScope term) normal @?= True)
        | (name, term, normal) <- examples
        ]
    , testCase "ifStuck is its own normal form" $
        withFresh emptyScope $ \x ->
          let scope = extendScope x emptyScope
              term  = ifStuck (nameOf x)
          in alphaEquiv scope (nf scope term) term @?= True
    ]
