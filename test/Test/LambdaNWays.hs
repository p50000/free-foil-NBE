-- | Tests of the bridge to the lambda-n-ways harness: both NbE normalisers
-- agree with the reference one, and the conversions round-trip.
module Test.LambdaNWays (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified LambdaPi.LambdaNWays as LNW

tests :: TestTree
tests =
  testGroup "lambda-n-ways bridge" $
    [ testCase (nm ++ ": nfGeneric agrees with nfSubst") $
        LNW.aeq (LNW.nfGeneric t) (LNW.nfSubst t) @?= True
    | (nm, t) <- lcTerms
    ]
      ++ [ testCase (nm ++ ": nfMono agrees with nfSubst") $
             LNW.aeq (LNW.nfMono t) (LNW.nfSubst t) @?= True
         | (nm, t) <- lcTerms
         ]
      ++ [ testCase (nm ++ ": toLC . fromLC round-trips") $
             LNW.aeq (LNW.toLC (LNW.fromLC t)) t @?= True
         | (nm, t) <- lcTerms
         ]

lcTerms :: [(String, LNW.LC LNW.IdInt)]
lcTerms =
  [ ("id", lam 0 (var 0))
  , ("K", lam 0 (lam 1 (var 0)))
  , ("id id", LNW.App (lam 0 (var 0)) (lam 1 (var 1)))
  , ("2*2", LNW.App church2 church2)
  ]
  where
    var i = LNW.Var (LNW.IdInt i)
    lam i b = LNW.Lam (LNW.IdInt i) b
    church2 = lam 0 (lam 1 (LNW.App (var 0) (LNW.App (var 0) (var 1))))
