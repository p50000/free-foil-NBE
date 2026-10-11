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
    [ testGroup "nf agrees with reference nf on every example"
        [ testCase nm $
            alphaEquiv emptyScope (LL.nf emptyScope t) (LL.nfSubst emptyScope t) @?= True
        | (nm, t) <- LLE.examples
        ]
    , testCase "a let-bound definition is applied: letId is the identity" $
        llAlphaEq (LL.nf emptyScope LLE.letId) "\\y. y"
    , testCase "definition used twice: letChurch is Church four" $
        llAlphaEq (LL.nf emptyScope LLE.letChurch) "\\s. \\z. s (s (s (s z)))"
    , testCase "an inner let shadows the outer binding" $
        llAlphaEq (LL.nf emptyScope LLE.letShadow) "\\b. b b"
    , testCase "whnf reduces a top-level let (let is a head redex)" $
        llAlphaEq (LL.whnf emptyScope "let i = \\x. x in i") "\\x. x"
    , testCase "whnf leaves a let under a lambda untouched" $
        llAlphaEq (LL.whnf emptyScope LLE.letUnderLam) LLE.letUnderLam
    , testCase "nf, in contrast, reduces the let under the lambda" $
        llAlphaEq (LL.nf emptyScope LLE.letUnderLam) "\\f. f f"
    , testCase "an unused divergent binding is never evaluated (call-by-need)" $
        llAlphaEq (LL.nf emptyScope LLE.letUnused) "\\y. y"
    , testCase "a let bound to a neutral still reduces (open term)" $
        LLP.withFreeVars emptyScope Map.empty ["f"] $ \scope env ->
          case (,) <$> LLP.parseOpen scope env "let y = f in y y"
                   <*> LLP.parseOpen scope env "f f" of
            Left err            -> assertFailure ("parse failed: " ++ err)
            Right (t, expected) ->
              alphaEquiv scope (LL.nf scope t) expected @?= True
    ]
