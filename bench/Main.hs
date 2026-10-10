{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Microbenchmarks for lambda-pi normalisation. Each input is normalised by
-- the generic NbE ('nfNbe'), the monomorphic NbE ('Mono.nfMono') and the
-- reference substitution normaliser ('nf'); results are forced by walking the
-- whole normal form, as in free-foil's own benchmark.
module Main (main) where

import Test.Tasty.Bench hiding (nf)

import Control.Monad.Foil
import LambdaPi hiding (whnf)
import qualified LambdaPi.Monomorphic as Mono
import LambdaPi.Parser ()  -- IsString instance for writing terms as strings

-- | The size of a term, used to force the whole normal form.
sizeOf :: LambdaPi n -> Int
sizeOf = \case
  Var {}     -> 1
  App f x    -> 1 + sizeOf f + sizeOf x
  Lam _ body -> 1 + sizeOf body
  Pi dom _ b -> 1 + sizeOf dom + sizeOf b

-- | The Church numeral @n@: @\\s. \\z. s (s (... z))@ with @n@ applications.
churchN :: Int -> LambdaPi VoidS
churchN n =
  withFresh emptyScope $ \s ->
    Lam s $ withFresh (extendScope s emptyScope) $ \z ->
      let apply = App (Var (sink (nameOf s)))
       in Lam z (iterate apply (Var (nameOf z)) !! n)

-- | @'power' n m@ is @m@ to the @n@: the Church numeral @n@ applied to @m@,
-- which normalises to the Church numeral for @m ^ n@.
power :: Int -> Int -> LambdaPi VoidS
power n m = App (churchN n) (churchN m)

-- | Church multiplication and addition combinators.
multT, addT :: LambdaPi VoidS
multT = "\\m. \\n. \\s. m (n s)"
addT  = "\\m. \\n. \\s. \\z. m s (n s z)"

churchMul, churchAdd :: Int -> Int -> LambdaPi VoidS
churchMul a b = App (App multT (churchN a)) (churchN b)
churchAdd a b = App (App addT (churchN a)) (churchN b)

-- | The identity @\\x. x@.
idTerm :: LambdaPi VoidS
idTerm = withFresh emptyScope $ \x -> Lam x (Var (nameOf x))

-- | The identity built directly in a scope, for use as a domain at any depth.
idIn :: Distinct s => Scope s -> LambdaPi s
idIn scope = withFresh scope $ \x -> Lam x (Var (nameOf x))

-- | @n@ nested dependent function types @(x0 : id) -> (x1 : id) -> ... -> id@
-- with distinct, unused binders. There are no redexes, so a normaliser that
-- re-normalised each codomain would be exponential in @n@; this is the case
-- the value representation is designed around.
nestedPi :: Int -> LambdaPi VoidS
nestedPi = go emptyScope
  where
    go :: Distinct s => Scope s -> Int -> LambdaPi s
    go scope k
      | k <= 0 = idIn scope
      | otherwise =
          withFresh scope $ \x ->
            case assertDistinct x of
              Distinct ->
                Pi (idIn scope) x (go (extendScope x scope) (k - 1))

-- | @n@ nested identity redexes: @id (id (... id))@, normalising to @id@.
nestedRedexes :: Int -> LambdaPi VoidS
nestedRedexes n = iterate (App idTerm) idTerm !! n

-- | A chain of @n@ nested lets @let x0 = id in let x1 = x0 in ... in x_{n-1}@,
-- encoded as @(\\x0. (\\x1. ... x_{n-1}) x0) id@ since lambda-pi has no @let@.
-- Each binding copies the previous one, so substitution performs @n@ copies.
nestedLet :: Int -> LambdaPi VoidS
nestedLet n =
  withFresh emptyScope $ \x0 ->
    case assertDistinct x0 of
      Distinct ->
        App (Lam x0 (go (extendScope x0 emptyScope) (nameOf x0) (n - 1))) idTerm
  where
    go :: Distinct s => Scope s -> Name s -> Int -> LambdaPi s
    go _ prev k | k <= 0 = Var prev
    go scope prev k =
      withFresh scope $ \xi ->
        case assertDistinct xi of
          Distinct ->
            App (Lam xi (go (extendScope xi scope) (nameOf xi) (k - 1))) (Var prev)

-- | Normalise @t@ three ways and force each result fully.
compareNormalisers :: String -> LambdaPi VoidS -> Benchmark
compareNormalisers name t =
  bgroup name
    [ bench "nfNbe"  $ whnf (sizeOf . nfNbe emptyScope) t
    , bench "nfMono" $ whnf (sizeOf . Mono.nfMono emptyScope) t
    , bench "nf"     $ whnf (sizeOf . nf emptyScope) t
    ]

main :: IO ()
main =
  defaultMain
    [ bgroup "Church m^n"
        [ compareNormalisers "8^2 = 64"    (power 2 8)
        , compareNormalisers "4^3 = 64"    (power 3 4)
        , compareNormalisers "2^8 = 256"   (power 8 2)
        , compareNormalisers "2^10 = 1024" (power 10 2)
        ]
    , bgroup "Church arithmetic"
        [ compareNormalisers "mult 8 8 = 64"     (churchMul 8 8)
        , compareNormalisers "mult 16 16 = 256"  (churchMul 16 16)
        , compareNormalisers "add 100 100 = 200" (churchAdd 100 100)
        , compareNormalisers "add 400 400 = 800" (churchAdd 400 400)
        ]
    , bgroup "Nested application redexes"
        [ compareNormalisers "depth 100"  (nestedRedexes 100)
        , compareNormalisers "depth 500"  (nestedRedexes 500)
        , compareNormalisers "depth 1000" (nestedRedexes 1000)
        ]
    , bgroup "Nested let (faithful)"
        [ compareNormalisers "depth 100"  (nestedLet 100)
        , compareNormalisers "depth 500"  (nestedLet 500)
        , compareNormalisers "depth 1000" (nestedLet 1000)
        ]
    , bgroup "Nested Pi types"
        [ compareNormalisers "depth 100"  (nestedPi 100)
        , compareNormalisers "depth 500"  (nestedPi 500)
        , compareNormalisers "depth 1000" (nestedPi 1000)
        ]
    ]
