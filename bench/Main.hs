{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Microbenchmarks for lambda-pi normalisation. Each input is normalised by
-- the generic NbE ('nf'), the monomorphic NbE ('Mono.nf') and the
-- reference substitution normaliser ('nfSubst'); results are forced by walking the
-- whole normal form, as in free-foil's own benchmark.
module Main (main) where

import Test.Tasty.Bench hiding (nf)

import Control.Monad.Foil
import LambdaPi hiding (whnf)
import qualified LambdaPi.Monomorphic as Mono
import LambdaPi.Parser ()  -- IsString instance for writing terms as strings

import Control.Monad.Free.Foil (AST (..), ScopedAST (..))
import Data.Bifoldable (Bifoldable, bifoldMap)
import Data.Monoid (Sum (..))
import Data.String (fromString)
import qualified Fragments.Combined as Composed
import qualified Monolith
import Monolith.Parser ()  -- IsString instance for the monolithic language

-- | The size of a term of any language, used to force the whole normal form.
-- A signature's 'bifoldMap' must inline for this to cost no more than the
-- traversal itself: small signatures and sums of them inline on their own,
-- and the monolith's instance carries an @INLINE@ pragma.
sizeOf :: Bifoldable sig => AST binder sig n -> Int
sizeOf = \case
  Var _     -> 1
  Node node -> 1 + getSum (bifoldMap (\(ScopedAST _ body) -> Sum (sizeOf body)) (Sum . sizeOf) node)

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

-- | A lambda-pi term in the monolithic language, through its printer and the
-- monolith's parser: the lambda syntax is the same.
monolithic :: LambdaPi VoidS -> Monolith.Monolith VoidS
monolithic = fromString . show

-- | The numeral @n@ as a string.
natural :: Int -> String
natural 0 = "zero"
natural k = "suc (" ++ natural (k - 1) ++ ")"

-- | @m * n@ by primitive recursion, with addition inlined.
natMul :: Int -> Int -> Monolith.Monolith VoidS
natMul m n = fromString $
  "(\\m. \\n. natrec m { zero -> zero ; suc (k, r) -> "
    ++ "(\\a. \\b. natrec a { zero -> b ; suc (k', r') -> suc r' }) n r }) "
    ++ "(" ++ natural m ++ ") (" ++ natural n ++ ")"

-- | Normalise a lambda-pi term by the generic NbE of lambda-pi, by the
-- monolithic language and by the composed one.
compareComposition :: String -> LambdaPi VoidS -> Benchmark
compareComposition name t =
  bgroup name
    [ bench "lambda-pi" $ whnf (sizeOf . nf emptyScope) t
    , bench "monolith"  $ whnf (sizeOf . Monolith.nf emptyScope) tm
    , bench "composed"  $ whnf (sizeOf . Composed.nf emptyScope) (Composed.fromMonolith tm)
    ]
  where
    tm = monolithic t

-- | Normalise a term of the full language by the monolithic and the composed
-- normaliser.
compareComposed :: String -> Monolith.Monolith VoidS -> Benchmark
compareComposed name tm =
  bgroup name
    [ bench "monolith" $ whnf (sizeOf . Monolith.nf emptyScope) tm
    , bench "composed" $ whnf (sizeOf . Composed.nf emptyScope) (Composed.fromMonolith tm)
    ]

-- | Normalise @t@ three ways and force each result fully.
compareNormalisers :: String -> LambdaPi VoidS -> Benchmark
compareNormalisers name t =
  bgroup name
    [ bench "generic" $ whnf (sizeOf . nf emptyScope) t
    , bench "mono"    $ whnf (sizeOf . Mono.nf emptyScope) t
    , bench "subst"   $ whnf (sizeOf . nfSubst emptyScope) t
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
    , bgroup "Composed vs monolith"
        [ compareComposition "Church mult 16 16 = 256" (churchMul 16 16)
        , compareComposition "Church 2^10 = 1024"      (power 10 2)
        , compareComposed    "natrec mult 16 16 = 256" (natMul 16 16)
        , compareComposed    "natrec mult 32 32 = 1024" (natMul 32 32)
        ]
    ]
