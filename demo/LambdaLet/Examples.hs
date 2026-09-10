{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Example lambda-let terms — the demo file of the language, meant to be
-- played with from the REPL:
--
-- > cabal repl lambda-let-demo
-- > ghci> import LambdaLet.Examples
-- > ghci> nfNbe emptyScope letChurch
-- > \s. \z. s (s (s (s z)))
--
-- Each example states its normal form and what it demonstrates about @let@.
-- Written as string literals (parsed by "LambdaLet.Parser") so the concrete
-- syntax doubles as documentation.
module LambdaLet.Examples
  ( letId
  , letChurch
  , letShadow
  , letUnderLam
  , letSharing
  , examples
  ) where

import FreeFoil.NbE (S (VoidS))
import LambdaLet (LambdaLet)
import LambdaLet.Parser ()

-- | @let@ as a definition: bind the identity, apply it to itself.
-- Normalises to @\\y. y@.
letId :: LambdaLet VoidS
letId = "let id = \\x. x in id id"

-- | A Church-numeral computation phrased with a definition:
-- @let two = \\s. \\z. s (s z) in two two@. Normalises to Church 4 — the
-- @let@-bound definition is used as a function and disappears entirely.
letChurch :: LambdaLet VoidS
letChurch = "let two = \\s. \\z. s (s z) in two two"

-- | Shadowing: the inner @let@ rebinds @x@, and scope-safe syntax makes the
-- occurrence unambiguously refer to the inner binding. Normalises to
-- @\\b. b b@ (the outer binding is unused).
letShadow :: LambdaLet VoidS
letShadow = "let x = \\a. a in let x = \\b. b b in x"

-- | A @let@ under a lambda. 'LambdaLet.nf'\/'FreeFoil.NbE.nfNbe' reduce it
-- (to @\\f. f f@); 'FreeFoil.NbE.whnfNbe' leaves it untouched, because
-- weak-head normalisation stops at binders — the lambda body is a scoped
-- position, and the @let@ inside it is exactly the kind of redex 'whnfNbe'
-- deliberately does not touch.
letUnderLam :: LambdaLet VoidS
letUnderLam = "\\f. let y = f in y y"

-- | Sharing: the bound expression is itself a redex, used twice. NbE
-- evaluates @(\\a. a) (\\b. b)@ /once/, when the @let@ extends the
-- environment; a substitution-based normaliser copies the redex into both
-- occurrences and reduces it twice. Same normal form (@\\z. z@), different
-- work — the first taste of why @let@ matters for evaluators even before
-- glued evaluation. (See @FEATURE_ZOO_DESIGN.md@ on top-level definitions
-- and lazy unfolding.)
letSharing :: LambdaLet VoidS
letSharing = "let d = (\\a. a) (\\b. b) in d d"

-- | All examples with their names, for harnesses and tests.
examples :: [(String, LambdaLet VoidS)]
examples =
  [ ("letId", letId)
  , ("letChurch", letChurch)
  , ("letShadow", letShadow)
  , ("letUnderLam", letUnderLam)
  , ("letSharing", letSharing)
  ]
