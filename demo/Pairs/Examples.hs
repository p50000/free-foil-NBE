{-# LANGUAGE RankNTypes #-}
-- | Example pairs terms, each with its normal form. The language has no
-- closed terms, so every example names its free variables and is parsed in
-- a scope by 'withOpenExample', as the open examples of lambda-pi are.
module Pairs.Examples
  ( OpenExample (..)
  , fstPair
  , sndPair
  , nestedProjections
  , pairOfRedexes
  , swap
  , splitOfRedex
  , splitNested
  , splitShadow
  , fstStuck
  , splitStuck
  , redexUnderSplit
  , projectionOfStuckSplit
  , stuckInsidePair
  , examples
  , withOpenExample
  ) where

import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Pairs
import Pairs.Parser (parseOpen, withFreeVars)

-- | An example with free variables: their names, outermost first, then the
-- term and its normal form, as strings.
data OpenExample = OpenExample [String] String String

-- | A projection of a pair; normalises to the component.
fstPair :: OpenExample
fstPair = OpenExample ["a", "b"] "fst (a, b)" "a"

-- | The other projection.
sndPair :: OpenExample
sndPair = OpenExample ["a", "b"] "snd (a, b)" "b"

-- | Projections nest: @fst (snd (a, (b, c)))@ normalises to @b@.
nestedProjections :: OpenExample
nestedProjections = OpenExample ["a", "b", "c"] "fst (snd (a, (b, c)))" "b"

-- | Redexes inside a pair are reduced; normalises to @(b, a)@.
pairOfRedexes :: OpenExample
pairOfRedexes = OpenExample ["a", "b"] "(snd (a, b), fst (a, b))" "(b, a)"

-- | @split@ on a pair binds both components; normalises to @(b, a)@.
swap :: OpenExample
swap = OpenExample ["a", "b"] "split (a, b) as (x, y) in (y, x)" "(b, a)"

-- | The scrutinee holds a redex in a component; normalises to @a@.
splitOfRedex :: OpenExample
splitOfRedex = OpenExample ["a", "b", "c"] "split (fst (a, b), c) as (x, y) in x" "a"

-- | A nested pair taken apart by two splits; normalises to @(c, (b, a))@.
splitNested :: OpenExample
splitNested =
  OpenExample ["a", "b", "c"]
    "split (a, (b, c)) as (x, p) in split p as (y, z) in (z, (y, x))"
    "(c, (b, a))"

-- | The inner pattern shadows both names of the outer one; normalises to @b@.
splitShadow :: OpenExample
splitShadow =
  OpenExample ["a", "b"]
    "split (a, b) as (x, y) in split (y, x) as (x, y) in x"
    "b"

-- | A projection of a variable is stuck and is its own normal form.
fstStuck :: OpenExample
fstStuck = OpenExample ["a"] "fst a" "fst a"

-- | A @split@ of a variable is stuck and is its own normal form.
splitStuck :: OpenExample
splitStuck =
  OpenExample ["a"] "split a as (x, y) in (y, x)" "split a as (x, y) in (y, x)"

-- | A redex under the two names of a stuck @split@: @nf@ reduces it, while
-- @whnf@ stops at the binder and leaves it in place.
redexUnderSplit :: OpenExample
redexUnderSplit =
  OpenExample ["a"]
    "split a as (x, y) in (fst (y, x), x)"
    "split a as (x, y) in (y, x)"

-- | A projection of a stuck @split@ is stuck too.
projectionOfStuckSplit :: OpenExample
projectionOfStuckSplit =
  OpenExample ["a"]
    "fst (split a as (x, y) in (y, x))"
    "fst (split a as (x, y) in (y, x))"

-- | A stuck projection next to a reducible one; normalises to @(fst a, b)@.
stuckInsidePair :: OpenExample
stuckInsidePair = OpenExample ["a", "b"] "(fst a, snd (a, b))" "(fst a, b)"

-- | The examples with their names.
examples :: [(String, OpenExample)]
examples =
  [ ("fstPair",                fstPair)
  , ("sndPair",                sndPair)
  , ("nestedProjections",      nestedProjections)
  , ("pairOfRedexes",          pairOfRedexes)
  , ("swap",                   swap)
  , ("splitOfRedex",           splitOfRedex)
  , ("splitNested",            splitNested)
  , ("splitShadow",            splitShadow)
  , ("fstStuck",               fstStuck)
  , ("splitStuck",             splitStuck)
  , ("redexUnderSplit",        redexUnderSplit)
  , ("projectionOfStuckSplit", projectionOfStuckSplit)
  , ("stuckInsidePair",        stuckInsidePair)
  ]

-- | Parse an example in a scope that holds its free variables, and continue
-- with the scope, the term and its normal form.
withOpenExample
  :: OpenExample
  -> (forall n. Distinct n => Scope n -> Pairs n -> Pairs n -> r)
  -> r
withOpenExample (OpenExample vars term normal) k =
  withFreeVars emptyScope Map.empty vars $ \scope env ->
    k scope (parse scope env term) (parse scope env normal)
  where
    parse scope env =
      either (error . ("Pairs.Examples: " ++)) id . parseOpen scope env
