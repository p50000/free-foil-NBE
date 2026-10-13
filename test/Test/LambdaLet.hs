{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Tests of lambda-let: the examples against their normal forms, the
-- weak-head normal form, and a let bound to a neutral.
module Test.LambdaLet (tests) where

import qualified Data.Map.Strict as Map

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil
import qualified LambdaLet as LL
import qualified LambdaLet.Examples as LLE
import qualified LambdaLet.Parser as LLP

llAlphaEq :: LL.LambdaLet VoidS -> LL.LambdaLet VoidS -> Assertion
llAlphaEq a b = alphaEquiv emptyScope a b @?= True

tests :: TestTree
tests =
  testGroup "lambda-let"
    [ testGroup "every example reaches its normal form"
        [ testGroup name
            [ testCase "nfSubst" (llAlphaEq (LL.nfSubst emptyScope term) normal)
            , testCase "nf"      (llAlphaEq (LL.nf emptyScope term) normal)
            ]
        | (name, term, normal) <- LLE.examples
        ]
    , testGroup "whnf"
        [ testCase "reduces a top-level let (let is a head redex)" $
            llAlphaEq (LL.whnf emptyScope "let i = \\x. x in i") "\\x. x"
        , testCase "leaves a let under a lambda untouched" $
            llAlphaEq (LL.whnf emptyScope LLE.letUnderLam) LLE.letUnderLam
        ]
    , testCase "a let bound to a neutral still reduces (open term)" $
        LLP.withFreeVars emptyScope Map.empty ["f"] $ \scope env ->
          case (,) <$> LLP.parseOpen scope env "let y = f in y y"
                   <*> LLP.parseOpen scope env "f f" of
            Left err            -> assertFailure ("parse failed: " ++ err)
            Right (t, expected) ->
              alphaEquiv scope (LL.nf scope t) expected @?= True
    ]
