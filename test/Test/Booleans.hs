{-# LANGUAGE LambdaCase #-}
-- | Tests of Booleans, the second 'FreeFoil.NbE.Eval' instance: @if@ on
-- constants and on a neutral condition.
module Test.Booleans (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil
import qualified Booleans as B

-- | A Boolean normal form, compared by plain equality: there are no binders.
data SB = SBTrue | SBFalse | SBIf SB SB SB | SBVar Int
  deriving (Eq, Show)

sb :: B.BoolTm n -> SB
sb = \case
  B.TT       -> SBTrue
  B.FF       -> SBFalse
  B.If c t f -> SBIf (sb c) (sb t) (sb f)
  Var x      -> SBVar (nameId x)
  _          -> error "sb: unexpected term"

tests :: TestTree
tests =
  testGroup "booleans (second Eval instance)"
    [ testCase "if true selects the then-branch" $
        sb (B.nf emptyScope (B.If B.TT B.TT B.FF)) @?= SBTrue
    , testCase "if false selects the else-branch" $
        sb (B.nf emptyScope (B.If B.FF B.TT B.FF)) @?= SBFalse
    , testCase "a reducible condition is evaluated first" $
        sb (B.nf emptyScope (B.If (B.If B.TT B.FF B.TT) B.TT B.FF)) @?= SBFalse
    , testCase "an if stuck on a neutral condition is preserved" $
        withFresh emptyScope $ \x ->
          let scope = extendScope x emptyScope
              term  = B.If (Var (nameOf x)) B.TT B.FF
           in sb (B.nf scope term) @?= SBIf (SBVar (nameId (nameOf x))) SBTrue SBFalse
    ]
