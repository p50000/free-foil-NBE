{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Definitions with glue, on the composed language: the folded readback
-- keeps the defined names, the unfolded readback agrees with the plain
-- unfolded environment, and conversion compares defined names folded first,
-- without unfolding them.
module Test.Glue (tests) where

import           Data.Map.Strict          (Map)
import qualified Data.Map.Strict          as Map
import           System.Timeout           (timeout)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil  (alphaEquiv)
import           FreeFoil.NbE.Definitions (Definitions (..), convertibleIn, nfUnfolded, nfWith)
import           FreeFoil.NbE.Glue        (Unfolding (..))

import           Fragments.Combined       (Pat, Sig)
import qualified Monolith.Parser
import           Test.Fragments           (budgeted, natural, parseIn, resolve)
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
      , testProperty "agrees with the unfolded environment" propUnfolded
      ]
  , testGroup "conversion under definitions"
      [ convertibleCase "a name and its unfolding" arith "four" plusTwoTwo True
      , convertibleCase "a name and its normal form" arith "four" (natural 4) True
      , convertibleCase "two different names" arith "four" "two" False
      , testCase "compares folded sides without unfolding" $
          withFree ["f"] $ \scope env ->
            withDefs scope env omega $ \defs scope' env' _ -> do
              let t = parseIn scope' env' "f omega"
              result <- timeout 1000000 (pure $! convertibleIn scope defs t t)
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

-- | A definition whose body has no normal form.
omega :: [(String, String)]
omega = [("omega", "(\\w. w w) (\\w. w w)")]

withFree :: [String] -> (forall n. Distinct n => Scope n -> Map String (Name n) -> r) -> r
withFree = Monolith.Parser.withFreeVars emptyScope Map.empty

-- | Build a telescope from raw definitions. The continuation also receives
-- the embedding of the outer scope into the scope of the definitions.
withDefs ::
  forall n r. Distinct n =>
  Scope n ->
  Map String (Name n) ->
  [(String, String)] ->
  (forall l. Distinct l => Definitions Pat Sig n l -> Scope l -> Map String (Name l) -> (forall e. Sinkable e => e n -> e l) -> r) ->
  r
withDefs scope0 env0 definitions k = go scope0 env0 NoDefinitions id definitions
  where
    go ::
      forall m. Distinct m =>
      Scope m -> Map String (Name m) -> Definitions Pat Sig n m -> (forall e. Sinkable e => e n -> e m) -> [(String, String)] -> r
    go scope env defs embed [] = k defs scope env embed
    go scope env defs embed ((x, t) : rest) =
      withFresh scope $ \b ->
        go (extendScope b scope) (Map.insert x (nameOf b) (Map.map sink env))
           (Define defs b (parseIn scope env t)) (sink . embed) rest

readsBackAs :: Unfolding -> String -> [(String, String)] -> String -> String -> TestTree
readsBackAs mode name definitions t expected = testCase name $
  withDefs emptyScope Map.empty definitions $ \defs scope env _ ->
    let result = nfWith mode emptyScope defs (parseIn scope env t)
    in assertBool (show result) (alphaEquiv scope result (parseIn scope env expected))

folded, unfolded :: String -> [(String, String)] -> String -> String -> TestTree
folded = readsBackAs Folded
unfolded = readsBackAs Unfolded

convertibleCase :: String -> [(String, String)] -> String -> String -> Bool -> TestTree
convertibleCase name definitions t u expected = testCase name $
  withDefs emptyScope Map.empty definitions $ \defs scope env _ ->
    convertibleIn emptyScope defs (parseIn scope env t) (parseIn scope env u) @?= expected

-- | On random mixed terms over the arithmetic definitions and two free
-- variables, the unfolded readback of the glued environment agrees with
-- 'nfUnfolded', the plain unfolded environment. Terms contain functions, so
-- a case is discarded when the plain normal form does not finish.
propUnfolded :: Property
propUnfolded =
  forAll (sized (genTerm (map fst arith ++ freeNames))) $ \raw ->
    withFree freeNames $ \scope env ->
      withDefs scope env arith $ \defs scope' env' embed ->
        let t = resolve scope' env' raw
            plain = nfUnfolded scope defs t
        in ioProperty $ budgeted plain $ \plain' ->
             alphaEquiv scope' (nfWith Unfolded scope defs t) (embed plain')
  where
    freeNames = ["a", "b"]
