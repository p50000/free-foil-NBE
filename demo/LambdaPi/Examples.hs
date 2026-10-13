{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
-- | Example lambda-pi terms, each with its normal form. The closed examples
-- are string literals parsed by "LambdaPi.Parser", except 'two', which is
-- built from the pattern synonyms. The open examples name their free
-- variables and are parsed in a scope by 'withOpenExample'.
module LambdaPi.Examples
  ( -- * Closed examples
    two
  , appTwo
  , idId
  , kDrop
  , underLam
  , underTwoLams
  , nestedApps
  , piCodomain
  , piNeutral
  , piArrow
  , piUnderLam
  , examples
    -- * Open examples
  , OpenExample (..)
  , neutralApp
  , neutralArg
  , openExamples
  , withOpenExample
  ) where

import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import LambdaPi
import LambdaPi.Parser (parseOpen, withFreeVars)

-- | The Church numeral two, built by hand: a fresh binder for @s@, another
-- for @z@ in the extended scope, and @s@ sunk into it. Normal already.
two :: LambdaPi VoidS
two = withFresh emptyScope
  (\ s -> Lam s $ withFresh (extendScope s emptyScope)
    (\ z -> Lam z (App (Var (sink (nameOf s)))
                       (App (Var (sink (nameOf s)))
                            (Var (nameOf z))))))

-- | Church two applied to itself; normalises to Church four.
appTwo :: LambdaPi VoidS
appTwo = App two two

-- | The identity applied to the identity; normalises to @\\z. z@.
idId :: LambdaPi VoidS
idId = "(\\x. x) (\\y. y)"

-- | The K combinator drops its second argument; normalises to @\\z. z@.
kDrop :: LambdaPi VoidS
kDrop = "(\\x. \\y. x) (\\a. a) (\\b. \\c. b)"

-- | A redex under a lambda: @nf@ reduces it to @\\g. g@, while @whnf@ stops
-- at the binder and leaves it in place.
underLam :: LambdaPi VoidS
underLam = "\\f. (\\x. x) f"

-- | A redex under two lambdas; normalises to @\\g. \\w. g w@.
underTwoLams :: LambdaPi VoidS
underTwoLams = "\\f. \\y. (\\x. x) (f y)"

-- | Nested applications with a redex in argument position; normalises to
-- @\\f. \\g. \\x. f (g x) x@.
nestedApps :: LambdaPi VoidS
nestedApps = "\\f. \\g. \\x. f (g x) ((\\y. y) x)"

-- | A redex in the codomain of a @Pi@; normalises to @(a : \\t. t) -> a@.
piCodomain :: LambdaPi VoidS
piCodomain = "(a : \\t. t) -> (\\y. y) a"

-- | A neutral codomain under a lambda; normal already.
piNeutral :: LambdaPi VoidS
piNeutral = "\\f. (a : f) -> f a"

-- | A non-dependent arrow, a @Pi@ whose binder is unused; normal already.
piArrow :: LambdaPi VoidS
piArrow = "(q : \\z. z) -> \\w. w"

-- | A redex in a @Pi@ codomain under a lambda: @nf@ reduces it to
-- @\\f. (a : f) -> a@, while @whnf@ leaves it in place.
piUnderLam :: LambdaPi VoidS
piUnderLam = "\\f. (a : f) -> (\\y. y) a"

-- | The closed examples with their names and normal forms.
examples :: [(String, LambdaPi VoidS, LambdaPi VoidS)]
examples =
  [ ("two",          two,          "\\s. \\z. s (s z)")
  , ("appTwo",       appTwo,       "\\s. \\z. s (s (s (s z)))")
  , ("idId",         idId,         "\\z. z")
  , ("kDrop",        kDrop,        "\\z. z")
  , ("underLam",     underLam,     "\\g. g")
  , ("underTwoLams", underTwoLams, "\\g. \\w. g w")
  , ("nestedApps",   nestedApps,   "\\f. \\g. \\x. f (g x) x")
  , ("piCodomain",   piCodomain,   "(a : \\t. t) -> a")
  , ("piNeutral",    piNeutral,    piNeutral)
  , ("piArrow",      piArrow,      piArrow)
  , ("piUnderLam",   piUnderLam,   "\\f. (a : f) -> a")
  ]

-- | An example with free variables: their names, outermost first, then the
-- term and its normal form, as strings.
data OpenExample = OpenExample [String] String String

-- | @f ((\\x. x) g)@: the argument's redex is reduced and the stuck
-- application stays, so the normal form is the neutral @f g@.
neutralApp :: OpenExample
neutralApp = OpenExample ["f", "g"] "f ((\\x. x) g)" "f g"

-- | @(\\x. a x) (b a)@: a β-step whose result, @a (b a)@, is neutral.
neutralArg :: OpenExample
neutralArg = OpenExample ["a", "b"] "(\\x. a x) (b a)" "a (b a)"

-- | The open examples with their names.
openExamples :: [(String, OpenExample)]
openExamples =
  [ ("neutralApp", neutralApp)
  , ("neutralArg", neutralArg)
  ]

-- | Parse an open example in a scope that holds its free variables, and
-- continue with the scope, the term and its normal form.
withOpenExample
  :: OpenExample
  -> (forall n. Distinct n => Scope n -> LambdaPi n -> LambdaPi n -> r)
  -> r
withOpenExample (OpenExample vars term normal) k =
  withFreeVars emptyScope Map.empty vars $ \scope env ->
    k scope (parse scope env term) (parse scope env normal)
  where
    parse scope env =
      either (error . ("LambdaPi.Examples: " ++)) id . parseOpen scope env
