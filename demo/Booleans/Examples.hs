{-# LANGUAGE DataKinds #-}
-- | Example Boolean terms, each with its normal form. There is no parser, so
-- they are built from the pattern synonyms of "Booleans".
module Booleans.Examples
  ( ifTrue
  , ifFalse
  , ifNested
  , ifStuck
  , examples
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Booleans

-- | @if true then true else false@; normalises to @true@.
ifTrue :: BoolTm VoidS
ifTrue = If TT TT FF

-- | @if false then true else false@; normalises to @false@.
ifFalse :: BoolTm VoidS
ifFalse = If FF TT FF

-- | The condition is an @if@ itself and is evaluated first; normalises to
-- @false@.
ifNested :: BoolTm VoidS
ifNested = If (If TT FF TT) TT FF

-- | @if x then true else false@ for a variable @x@ in scope: the @if@ is
-- stuck on the neutral condition and is its own normal form.
ifStuck :: Name n -> BoolTm n
ifStuck x = If (Var x) TT FF

-- | The closed examples with their names and normal forms.
examples :: [(String, BoolTm VoidS, BoolTm VoidS)]
examples =
  [ ("ifTrue",   ifTrue,   TT)
  , ("ifFalse",  ifFalse,  FF)
  , ("ifNested", ifNested, FF)
  ]
