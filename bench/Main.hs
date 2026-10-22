{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import FreeFoil.NbE.Conversion (convertibleUnder)
import FreeFoil.NbE.Definitions (Definitions (..), convertibleIn, definitionsEnv, nfFolded, nfUnfolded, nfWith)
import FreeFoil.NbE.Glue (Unfolding (..))
import qualified Monolith.Parser as MonolithParser

-- | The size of a term of any language, used to force the whole normal form.
-- A signature's 'bifoldMap' must inline for this to cost no more than the
-- traversal itself. Small signatures and sums of them inline on their own,
-- and @mkFreeFoil@ generates the instances of a large one with @INLINE@
-- pragmas.
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

-- | A telescope of definitions of the composed language, each body parsed in
-- the scope of the names before it, with the scope and the names it binds.
withProgram ::
  forall r.
  [(String, String)] ->
  (forall l. Distinct l => Definitions Composed.Pat Composed.Sig VoidS l -> Scope l -> Map String (Name l) -> r) ->
  r
withProgram = go emptyScope Map.empty NoDefinitions
  where
    go ::
      forall m. Distinct m =>
      Scope m ->
      Map String (Name m) ->
      Definitions Composed.Pat Composed.Sig VoidS m ->
      [(String, String)] ->
      (forall l. Distinct l => Definitions Composed.Pat Composed.Sig VoidS l -> Scope l -> Map String (Name l) -> r) ->
      r
    go scope names defs [] k = k defs scope names
    go scope names defs ((x, body) : rest) k =
      withFresh scope $ \b ->
        go (extendScope b scope) (Map.insert x (nameOf b) (Map.map sink names))
           (Define defs b (parseComposed scope names body)) rest k

-- | A term of the composed language with the given free names.
parseComposed :: Distinct n => Scope n -> Map String (Name n) -> String -> Composed.Combined n
parseComposed scope names = Composed.fromMonolith . either error id . MonolithParser.parseOpen scope names

-- | @plus@ by primitive recursion.
plusDefinition :: (String, String)
plusDefinition = ("plus", "\\m. \\n. natrec m { zero -> n ; suc (k, r) -> suc r }")

-- | @plus@ and @mult@ by primitive recursion.
arithmetic :: [(String, String)]
arithmetic =
  [ plusDefinition
  , ("mult", "\\m. \\n. natrec m { zero -> zero ; suc (k, r) -> plus n r }")
  ]

-- | @mult m n@ under the definitions, normalised with the plain unfolded
-- environment and with glue, read back unfolded and folded.
compareDefinitions :: String -> Int -> Int -> Benchmark
compareDefinitions name m n =
  withProgram arithmetic $ \defs scope names ->
    let t = parseComposed scope names ("mult (" ++ natural m ++ ") (" ++ natural n ++ ")")
    in bgroup name
         [ bench "plain, unfolded" $ whnf (sizeOf . nfUnfolded emptyScope defs) t
         , bench "glued, unfolded" $ whnf (sizeOf . nfWith Unfolded emptyScope defs) t
         , bench "glued, folded"   $ whnf (sizeOf . nfFolded emptyScope defs) t
         ]

-- | @d0 = 1@ and @dᵢ₊₁ = plus dᵢ dᵢ@ up to @dₖ₊₁@, so that @dᵢ@ unfolds to
-- the numeral @2ⁱ@.
doubling :: Int -> [(String, String)]
doubling k =
  plusDefinition : ("d0", "suc zero")
    : [ ("d" ++ show i, "plus d" ++ show (i - 1) ++ " d" ++ show (i - 1)) | i <- [1 .. k + 1] ]

-- | Check @t ≡ u@ under @'doubling' k@ with the plain unfolded environment
-- and with glue. Both build their environment inside the benchmarked
-- function, so that no iteration reuses the values of another.
compareConversion :: String -> Int -> String -> String -> Benchmark
compareConversion name k t u =
  withProgram (doubling k) $ \defs scope names ->
    let terms = (parseComposed scope names t, parseComposed scope names u)
    in bgroup name
         [ bench "plain" $ whnf
             (\ds -> let values = definitionsEnv emptyScope ds
                     in uncurry (convertibleUnder emptyScope values values) terms) defs
         , bench "glued" $ whnf (\ds -> uncurry (convertibleIn emptyScope ds) terms) defs
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
    , bgroup "Definitions: plain vs glued"
        [ compareDefinitions "mult 16 16 = 256"  16 16
        , compareDefinitions "mult 32 32 = 1024" 32 32
        ]
    , bgroup "Conversion under definitions: plain vs glued"
        [ compareConversion (name ++ ", 2^" ++ show k) k t u
        | k <- [8, 12]
        , (name, t, u) <-
            [ ("a definition and its body", "d" ++ show (k + 1), "plus d" ++ show k ++ " d" ++ show k)
            , ("a computation around a definition", "plus (suc zero) d" ++ show k, "suc d" ++ show k)
            , ("not convertible", "d" ++ show k, "suc d" ++ show k)
            ]
        ]
    ]
