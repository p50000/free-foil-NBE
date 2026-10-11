{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Tests of lambda-let: the examples against the reference normaliser,
-- sharing, shadowing, call-by-need and the weak-head normal form.
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
    [ testGroup "nfNbe agrees with reference nf on every example"
        [ testCase nm $
            alphaEquiv emptyScope (LL.nfNbe emptyScope t) (LL.nfSubst emptyScope t) @?= True
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
