{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
-- | Example naturals terms, each with its normal form. The closed examples
-- are string literals parsed by "Naturals.Parser"; arithmetic is primitive
-- recursion, with the inner recursions written out. The open examples name
-- their free variables and are parsed in a scope by 'withOpenExample'.
module Naturals.Examples
  ( -- * Closed examples
    two
  , plusTwoThree
  , multTwoThree
  , predThree
  , factThree
  , zeroBranch
  , examples
  , plusTerm
  , multTerm
    -- * Open examples
  , OpenExample (..)
  , natrecStuck
  , unfoldsOnce
  , predOfNeutral
  , redexUnderSucBranch
  , redexInZeroBranch
  , openExamples
  , withOpenExample
  ) where

import qualified Data.Map.Strict as Map
import Data.String (fromString)

import Control.Monad.Foil
import Naturals
import Naturals.Parser (parseOpen, withFreeVars)

-- | The numeral two; normal already.
two :: Naturals VoidS
two = "suc (suc zero)"

-- | @2 + 3@: recursion on the first summand, the step applies @suc@ to the
-- recursive result; normalises to five.
plusTwoThree :: Naturals VoidS
plusTwoThree =
  "natrec (suc (suc zero)) { zero -> suc (suc (suc zero)) ; suc k, r -> suc r }"

-- | @2 * 3@: an inner recursion adds three to the recursive result of the
-- outer one; normalises to six.
multTwoThree :: Naturals VoidS
multTwoThree =
  "natrec (suc (suc zero)) { zero -> zero ; \
  \  suc k, r -> natrec (suc (suc (suc zero))) { zero -> r ; suc k', r' -> suc r' } }"

-- | The predecessor: the step returns @k@ and ignores the recursive result;
-- normalises to two.
predThree :: Naturals VoidS
predThree = "natrec (suc (suc (suc zero))) { zero -> zero ; suc k, r -> k }"

-- | @3!@: the step multiplies @suc k@ by the recursive result, with
-- multiplication and addition written out; normalises to six.
factThree :: Naturals VoidS
factThree =
  "natrec (suc (suc (suc zero))) { zero -> suc zero ; \
  \  suc k, r -> natrec (suc k) { zero -> zero ; \
  \    suc k', r' -> natrec r { zero -> r' ; suc k'', r'' -> suc r'' } } }"

-- | A recursion on @zero@ takes the zero branch; normalises to one.
zeroBranch :: Naturals VoidS
zeroBranch = "natrec zero { zero -> suc zero ; suc k, r -> r }"

-- | The closed examples with their names and normal forms.
examples :: [(String, Naturals VoidS, Naturals VoidS)]
examples =
  [ ("two",          two,          numeral 2)
  , ("plusTwoThree", plusTwoThree, numeral 5)
  , ("multTwoThree", multTwoThree, numeral 6)
  , ("predThree",    predThree,    numeral 2)
  , ("factThree",    factThree,    numeral 6)
  , ("zeroBranch",   zeroBranch,   numeral 1)
  ]

-- | The numeral @k@ as source text.
numeralSource :: Int -> String
numeralSource k = concat (replicate k "suc (") ++ "zero" ++ replicate k ')'

-- | @m + n@ by recursion on @m@.
plusTerm :: Int -> Int -> Naturals VoidS
plusTerm m n =
  fromString $
    "natrec " ++ numeralSource m ++ " { zero -> " ++ numeralSource n ++ " ; suc k, r -> suc r }"

-- | @m * n@ by recursion on @m@, adding @n@ to the recursive result.
multTerm :: Int -> Int -> Naturals VoidS
multTerm m n =
  fromString $
    "natrec " ++ numeralSource m ++ " { zero -> zero ; suc k, r -> natrec "
      ++ numeralSource n ++ " { zero -> r ; suc k', r' -> suc r' } }"

-- | An example with free variables: their names, outermost first, then the
-- term and its normal form, as strings.
data OpenExample = OpenExample [String] String String

-- | A recursion on a variable is stuck and is its own normal form.
natrecStuck :: OpenExample
natrecStuck =
  OpenExample ["a"]
    "natrec a { zero -> zero ; suc k, r -> suc r }"
    "natrec a { zero -> zero ; suc k, r -> suc r }"

-- | A recursion on @suc a@ unfolds once and is then stuck on @a@.
unfoldsOnce :: OpenExample
unfoldsOnce =
  OpenExample ["a", "b"]
    "natrec (suc a) { zero -> b ; suc k, r -> suc r }"
    "suc (natrec a { zero -> b ; suc k, r -> suc r })"

-- | The predecessor of @suc (suc a)@ is @suc a@: the step uses @k@ and the
-- stuck recursive result is never forced.
predOfNeutral :: OpenExample
predOfNeutral =
  OpenExample ["a"]
    "natrec (suc (suc a)) { zero -> zero ; suc k, r -> k }"
    "suc a"

-- | A redex under the two names of a stuck recursion: @nf@ reduces it, while
-- @whnf@ stops at the binder and leaves it in place.
redexUnderSucBranch :: OpenExample
redexUnderSucBranch =
  OpenExample ["a"]
    "natrec a { zero -> zero ; suc k, r -> natrec zero { zero -> r ; suc k', r' -> k' } }"
    "natrec a { zero -> zero ; suc k, r -> r }"

-- | A redex in the zero branch of a stuck recursion. The zero branch is a
-- term position, so even @whnf@ reduces it.
redexInZeroBranch :: OpenExample
redexInZeroBranch =
  OpenExample ["a", "b"]
    "natrec a { zero -> natrec (suc zero) { zero -> zero ; suc k, r -> b } ; suc k, r -> r }"
    "natrec a { zero -> b ; suc k, r -> r }"

-- | The open examples with their names.
openExamples :: [(String, OpenExample)]
openExamples =
  [ ("natrecStuck",         natrecStuck)
  , ("unfoldsOnce",         unfoldsOnce)
  , ("predOfNeutral",       predOfNeutral)
  , ("redexUnderSucBranch", redexUnderSucBranch)
  , ("redexInZeroBranch",   redexInZeroBranch)
  ]

-- | Parse an open example in a scope that holds its free variables, and
-- continue with the scope, the term and its normal form.
withOpenExample
  :: OpenExample
  -> (forall n. Distinct n => Scope n -> Naturals n -> Naturals n -> r)
  -> r
withOpenExample (OpenExample vars term normal) k =
  withFreeVars emptyScope Map.empty vars $ \scope env ->
    k scope (parse scope env term) (parse scope env normal)
  where
    parse scope env =
      either (error . ("Naturals.Examples: " ++)) id . parseOpen scope env
