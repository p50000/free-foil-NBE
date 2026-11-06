{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Definitions with glue, on the composed language: the folded readback
-- keeps the defined names, the unfolded readback gives the normal form, and
-- conversion compares defined names folded first, without unfolding them.
-- The tests follow those of #29.
module Test.Glue (tests) where

import           System.Timeout           (timeout)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Free.Foil  (alphaEquiv)
import qualified FreeFoil.NbE             as NbE
import           FreeFoil.NbE.Conversion  (convertible)
import           FreeFoil.NbE.Definitions (Unfolding (..), withUnfolding)

import           Test.Definitions         (withDefined)
import           Test.Fragments           (budgeted, natural, parseIn, resolve, withFree)
import           Test.Monolith            (genTerm)

tests :: TestTree
tests = testGroup "glue (composed language)"
  [ testGroup "folded readback"
      [ folded "keeps a defined name" arith "four" "four"
      , folded "under a constructor" arith "suc four" "suc four"
      , folded "keeps an application of a definition" arith plusTwoTwo plusTwoTwo
      , folded "through a projection" arith "fst (four, zero)" "four"
      , folded "under a binder" arith "\\y. plus y two" "\\y. plus y two"
      , folded "keeps an eliminator on a defined name" arith recTwo recTwo
      ]
  , testGroup "unfolded readback"
      [ unfolded "a defined name" arith "four" (natural 4)
      , unfolded "an eliminator on a defined name" arith recTwo (natural 2)
      , unfolded "under a binder" arith
          "\\y. plus y two"
          ("\\y. natrec y { zero -> " ++ natural 2 ++ " ; suc (k, r) -> suc r }")
      , testProperty "of the folded readback is the unfolded readback" propFoldedThenUnfolded
      ]
  , testGroup "conversion under definitions"
      [ convertibleCase "a name and its unfolding" arith "four" plusTwoTwo True
      , convertibleCase "a name and its normal form" arith "four" (natural 4) True
      , convertibleCase "two different names" arith "four" "two" False
      , convertibleCase "one name on different arguments with equal unfoldings" constant "k zero two" "k zero four" True
      , convertibleCase "one name on different arguments with different unfoldings" constant "k two zero" "k four zero" False
      , testCase "compares folded sides without unfolding" $
          withFree $ \scope0 env0 ->
            withDefined scope0 env0 omega $ \ctx scope env -> do
              let t = parseIn scope env "a omega"
              result <- timeout 1000000 (pure $! convertible scope ctx t t)
              result @?= Just True
      ]
  ]

-- * Programs

arith :: [(String, String)]
arith =
  [ ("two", natural 2)
  , ("plus", "\\m. \\n. natrec m { zero -> n ; suc (k, r) -> suc r }")
  , ("four", plusTwoTwo)
  ]

plusTwoTwo :: String
plusTwoTwo = "plus two two"

recTwo :: String
recTwo = "natrec two { zero -> zero ; suc (k, r) -> suc r }"

-- | A constant function over the arithmetic definitions, whose
-- applications agree folded only on equal arguments.
constant :: [(String, String)]
constant = arith ++ [("k", "\\x. \\y. x")]

-- | A definition whose body has no normal form.
omega :: [(String, String)]
omega = [("omega", "(\\w. w w) (\\w. w w)")]

readsBackAs :: Unfolding -> String -> [(String, String)] -> String -> String -> TestTree
readsBackAs unfolding name definitions t expected = testCase name $
  withFree $ \scope0 env0 ->
    withDefined scope0 env0 definitions $ \ctx scope env ->
      let result = NbE.nf scope (withUnfolding unfolding ctx) (parseIn scope env t)
      in assertBool (show result) (alphaEquiv scope result (parseIn scope env expected))

folded, unfolded :: String -> [(String, String)] -> String -> String -> TestTree
folded = readsBackAs Folded
unfolded = readsBackAs Unfolded

convertibleCase :: String -> [(String, String)] -> String -> String -> Bool -> TestTree
convertibleCase name definitions t u expected = testCase name $
  withFree $ \scope0 env0 ->
    withDefined scope0 env0 definitions $ \ctx scope env ->
      convertible scope ctx (parseIn scope env t) (parseIn scope env u) @?= expected

-- | On random mixed terms over the arithmetic definitions and the free
-- variables, normalising the folded normal form unfolds it to the normal
-- form. Terms contain functions, so a case is discarded when a normal form
-- does not finish.
propFoldedThenUnfolded :: Property
propFoldedThenUnfolded =
  forAll (sized (genTerm (map fst arith ++ ["a", "b"]))) $ \raw ->
    withFree $ \scope0 env0 ->
      withDefined scope0 env0 arith $ \ctx scope env ->
        let t = resolve scope env raw
            normal = NbE.nf scope ctx t
            foldedForm = NbE.nf scope (withUnfolding Folded ctx) t
        in ioProperty $ budgeted (normal, foldedForm) $ \(normal', folded') ->
             alphaEquiv scope (NbE.nf scope ctx folded') normal'
