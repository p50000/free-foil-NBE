{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Example lambda-let terms, written as string literals (parsed by
-- "LambdaLet.Parser"). Each states what it shows and its normal form.
module LambdaLet.Examples
  ( letId
  , letChurch
  , letShadow
  , letUnderLam
  , letSharing
  , letUnused
  , examples
  ) where

import Control.Monad.Foil
import LambdaLet (LambdaLet)
import LambdaLet.Parser ()

-- | A definition applied to itself; normalises to @\\y. y@.
letId :: LambdaLet VoidS
letId = "let id = \\x. x in id id"

-- | Church arithmetic through a definition; normalises to Church 4.
letChurch :: LambdaLet VoidS
letChurch = "let two = \\s. \\z. s (s z) in two two"

-- | The inner @let@ shadows the outer one; normalises to @\\b. b b@.
letShadow :: LambdaLet VoidS
letShadow = "let x = \\a. a in let x = \\b. b b in x"

-- | A @let@ under a lambda: @nfNbe@ reduces it to @\\f. f f@, while
-- @whnfNbe@ stops at the binder and leaves it in place.
letUnderLam :: LambdaLet VoidS
letUnderLam = "\\f. let y = f in y y"

-- | The bound redex is used twice but evaluated at most once: the environment
-- holds one shared thunk. Normalises to @\\z. z@.
letSharing :: LambdaLet VoidS
letSharing = "let d = (\\a. a) (\\b. b) in d d"

-- | An unused binding is never evaluated, even a divergent one (Ω here);
-- normalises to @\\y. y@. This is what makes @let@ call-by-need.
letUnused :: LambdaLet VoidS
letUnused = "let w = (\\x. x x) (\\x. x x) in \\y. y"

-- | All examples with their names, for harnesses and tests.
examples :: [(String, LambdaLet VoidS)]
examples =
  [ ("letId", letId)
  , ("letChurch", letChurch)
  , ("letShadow", letShadow)
  , ("letUnderLam", letUnderLam)
  , ("letSharing", letSharing)
  , ("letUnused", letUnused)
  ]
