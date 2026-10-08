{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

-- | The lambda-n-ways benchmark, @nf@, @random15@ and @random20@, over three
-- normalisers: the generic 'LP.nfNbe' through the "LambdaPi.LambdaNWays"
-- bridge, the monomorphic 'Mono.nfMono' over the same syntax, and the fork's
-- own hand-written foil NbE. Generic against monomorphic measures the cost of
-- the generic value domain; monomorphic against the fork, the cost of the
-- generic syntax. A check first confirms that both free-foil columns agree
-- with the fork, up to α, on every corpus term. The corpus directory is
-- @../lambda-n-ways-fork/lams/@ or @LAMS_DIR@.
module Main (main) where

import Control.DeepSeq (force, rnf)
import Control.Monad (forM_)
import Data.Maybe (fromMaybe)
import System.Environment (lookupEnv)
import Test.Tasty.Bench

import qualified Util.IdInt as U
import qualified Util.Syntax.Lambda as U
import Util.Impl (LambdaImpl (..), getTerm, getTerms, toIdInt)
import qualified Foil.NBE

import Control.Monad.Foil
import Control.Monad.Free.Foil
import qualified LambdaPi as LP
import qualified LambdaPi.LambdaNWays as LNW
import qualified LambdaPi.Monomorphic as Mono

-- The harness's LC and the bridge's LC are structurally identical.
toLNW :: U.LC U.IdInt -> LNW.LC LNW.IdInt
toLNW = \case
  U.Var (U.IdInt i)   -> LNW.Var (LNW.IdInt i)
  U.Lam (U.IdInt i) b -> LNW.Lam (LNW.IdInt i) (toLNW b)
  U.App f a           -> LNW.App (toLNW f) (toLNW a)

fromLNW :: LNW.LC LNW.IdInt -> U.LC U.IdInt
fromLNW = \case
  LNW.Var (LNW.IdInt i)   -> U.Var (U.IdInt i)
  LNW.Lam (LNW.IdInt i) b -> U.Lam (U.IdInt i) (fromLNW b)
  LNW.App f a             -> U.App (fromLNW f) (fromLNW a)

-- | The generic NbE as a harness implementation. The conversions run outside
-- the timed @impl_nf@, as for the fork's own column.
genericImpl :: LambdaImpl
genericImpl =
  LambdaImpl
    { impl_name = "NBE.FreeFoil (generic)",
      impl_fromLC = LNW.fromLC . toLNW,
      impl_toLC = fromLNW . LNW.toLC,
      impl_nf = LP.nfNbe emptyScope,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = alphaEquiv emptyScope
    }

-- | The monomorphic NbE over the same syntax; only @impl_nf@ differs.
monoImpl :: LambdaImpl
monoImpl =
  LambdaImpl
    { impl_name = "NBE.FreeFoil (monomorphic)",
      impl_fromLC = LNW.fromLC . toLNW,
      impl_toLC = fromLNW . LNW.toLC,
      impl_nf = Mono.nfMono emptyScope,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = alphaEquiv emptyScope
    }

impls :: [LambdaImpl]
impls = [genericImpl, monoImpl, Foil.NBE.impl]

benchOne :: LambdaImpl -> U.LC U.IdInt -> Benchmark
benchOne LambdaImpl{..} lc =
  let !tm = force (impl_fromLC lc)
   in bench impl_name (nf (rnf . impl_nf) tm)

benchMany :: LambdaImpl -> [U.LC U.IdInt] -> Benchmark
benchMany LambdaImpl{..} lcs =
  let !tms = force (map impl_fromLC lcs)
   in bench impl_name (nf (rnf . map impl_nf) tms)

-- | Normal form as a named term, through a given implementation.
nfLC :: LambdaImpl -> U.LC U.IdInt -> U.LC U.IdInt
nfLC LambdaImpl{..} = impl_toLC . impl_nf . impl_fromLC

-- | Does an implementation agree with the fork, up to α, on @t@?
agrees :: LambdaImpl -> U.LC U.IdInt -> Bool
agrees impl t =
  case Foil.NBE.impl of
    LambdaImpl{..} ->
      impl_aeq (impl_fromLC (nfLC impl t))
               (impl_fromLC (nfLC Foil.NBE.impl t))

main :: IO ()
main = do
  dir <- fromMaybe "../lambda-n-ways-fork/lams/" <$> lookupEnv "LAMS_DIR"
  lennart <- toIdInt <$> getTerm (dir ++ "lennart.lam")
  random15 <- getTerms (dir ++ "random15.lam")
  random20 <- getTerms (dir ++ "random20.lam")
  let corpus = lennart : random15 ++ random20
  forM_ [genericImpl, monoImpl] $ \impl -> do
    let bad = length (filter (not . agrees impl) corpus)
    putStrLn $ "correctness: " ++ impl_name impl ++ " vs fork baseline on "
      ++ show (length corpus) ++ " terms: "
      ++ (if bad == 0 then "ALL AGREE" else show bad ++ " MISMATCH(ES)")
  defaultMain
    [ bgroup "nf"       [ benchOne  i lennart  | i <- impls ]
    , bgroup "random15" [ benchMany i random15 | i <- impls ]
    , bgroup "random20" [ benchMany i random20 | i <- impls ]
    ]
