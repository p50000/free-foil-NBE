{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- The SPECIALIZE pragmas at a context of definitions are rules for the
-- library's functions.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Microbenchmarks for lambda-pi normalisation. Each input is normalised by
-- the generic NbE ('nf'), the monomorphic NbE ('Mono.nf') and the
-- reference substitution normaliser ('nfSubst'); results are forced by walking the
-- whole normal form, as in free-foil's own benchmark.
module Main (main) where

import Test.Tasty.Bench hiding (nf)

import Control.Monad.Foil
import FreeFoil.NbE (NoContext (..))
import qualified FreeFoil.NbE as NbE
import FreeFoil.NbE.Conversion (convertible, convertibleUnder)
import qualified FreeFoil.NbE.Conversion as Conv
import FreeFoil.NbE.Definitions (Defined, Unfolding (..), define, noDefinitions, withUnfolding)
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
import qualified Monolith.Parser as MonolithParser
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

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

-- | @\\f. \\x1. ... \\xk. f x1 ... xk@, the function variable η-expanded
-- @k@ times. It is convertible with @\\f. f@ by @k@ steps of η.
etaFunction :: Int -> String
etaFunction k =
  "\\f. " ++ concat [ "\\x" ++ show i ++ ". " | i <- [1 .. k] ]
    ++ unwords ("f" : [ "x" ++ show i | i <- [1 .. k] ])

-- | @\\p. t@ where @t@ is the pair @p@ η-expanded to depth @d@:
-- @(fst p, snd p)@ at depth 1, with each projection expanded again below.
-- It is convertible with @\\p. p@ by @2^d - 1@ steps of η.
etaPair :: Int -> String
etaPair d = "\\p. " ++ go "p" d
  where
    go e 0 = e
    go e k = "(" ++ go ("fst (" ++ e ++ ")") (k - 1) ++ ", " ++ go ("snd (" ++ e ++ ")") (k - 1) ++ ")"

-- | Check @t ≡ u@ by the generic conversion of lambda-pi and by the
-- monomorphic one.
compareConvertible :: String -> LambdaPi VoidS -> LambdaPi VoidS -> Benchmark
compareConvertible name t u =
  bgroup name
    [ bench "generic" $ whnf (uncurry (convertible emptyScope NoContext)) (t, u)
    , bench "mono"    $ whnf (uncurry (Mono.convertible emptyScope)) (t, u)
    ]

-- | Check @t ≡ u@ in lambda-pi, in the monolithic language and in the
-- composed one.
compareComposedConversion :: String -> LambdaPi VoidS -> LambdaPi VoidS -> Benchmark
compareComposedConversion name t u =
  bgroup name
    [ bench "lambda-pi" $ whnf (uncurry (convertible emptyScope NoContext)) (t, u)
    , bench "monolith"  $ whnf (uncurry (convertible emptyScope NoContext)) (tm, um)
    , bench "composed"  $ whnf (uncurry (convertible emptyScope NoContext)) (Composed.fromMonolith tm, Composed.fromMonolith um)
    ]
  where
    tm = monolithic t
    um = monolithic u

-- | Check @t ≡ u@ in the full language, monolithic and composed.
compareFullConversion :: String -> Monolith.Monolith VoidS -> Monolith.Monolith VoidS -> Benchmark
compareFullConversion name t u =
  bgroup name
    [ bench "monolith" $ whnf (uncurry (convertible emptyScope NoContext)) (t, u)
    , bench "composed" $ whnf (uncurry (convertible emptyScope NoContext)) (Composed.fromMonolith t, Composed.fromMonolith u)
    ]

-- | Normalise @t@ three ways and force each result fully.
compareNormalisers :: String -> LambdaPi VoidS -> Benchmark
compareNormalisers name t =
  bgroup name
    [ bench "generic" $ whnf (sizeOf . nf emptyScope) t
    , bench "mono"    $ whnf (sizeOf . Mono.nf emptyScope) t
    , bench "subst"   $ whnf (sizeOf . nfSubst emptyScope) t
    ]

-- * Definitions

-- | Definitions of the composed language, specialised as a client of the
-- library would. Without the pragma for 'Conv.convertible', the conversion
-- rows run the unspecialised check.
type DefinedComposed = Defined Composed.Pat Composed.Sig

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> DefinedComposed n -> Composed.Combined n -> Composed.Combined n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> DefinedComposed o -> Substitution Composed.Value i o -> Composed.Combined i -> Composed.Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> DefinedComposed n -> Composed.Value n -> Composed.Combined n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> DefinedComposed n -> Composed.Value n -> Composed.Value n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> DefinedComposed n -> Composed.Combined n -> Composed.Combined n -> Bool #-}

-- | A program of definitions of the composed language over the empty scope,
-- each body parsed in the scope of the names before it.
data Telescope l where
  Empty :: Telescope VoidS
  Define :: (Distinct m, DExt m l) => Telescope m -> Scope m -> NameBinder m l -> Composed.Combined m -> Telescope l

-- | Parse a program, with the scope and the names it binds.
withProgram ::
  forall r.
  [(String, String)] ->
  (forall l. Distinct l => Telescope l -> Scope l -> Map String (Name l) -> r) ->
  r
withProgram = go Empty emptyScope Map.empty
  where
    go ::
      forall m. Distinct m =>
      Telescope m -> Scope m -> Map String (Name m) -> [(String, String)] ->
      (forall l. Distinct l => Telescope l -> Scope l -> Map String (Name l) -> r) ->
      r
    go tele scope names [] k = k tele scope names
    go tele scope names ((x, body) : rest) k =
      withFresh scope $ \b ->
        go (Define tele scope b (parseComposed scope names body)) (extendScope b scope)
           (Map.insert x (nameOf b) (Map.map sink names)) rest k

-- | The definitions of a program as a context, glued.
definedOf :: Telescope l -> DefinedComposed l
definedOf = \case
  Empty -> noDefinitions
  Define tele scope x body -> define scope x body (definedOf tele)

-- | The definitions of a program as an environment, without glue: each
-- defined name maps to the value of its body.
environmentOf :: Telescope l -> Substitution Composed.Value l VoidS
environmentOf = \case
  Empty -> identitySubst
  Define tele _ x body ->
    let values = environmentOf tele
    in addSubst values x (NbE.eval emptyScope NoContext values body)

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

-- | @mult m n@ under the definitions: in the plain environment, and glued,
-- read back unfolded and folded. The context and the environment are built
-- inside the benchmarked function, so that no iteration reuses the values
-- of another.
compareDefinitions :: String -> Int -> Int -> Benchmark
compareDefinitions name m n =
  withProgram arithmetic $ \tele scope names ->
    let t = parseComposed scope names ("mult (" ++ natural m ++ ") (" ++ natural n ++ ")")
    in bgroup name
         [ bench "plain"           $ whnf (\d -> sizeOf (NbE.quote emptyScope NoContext (NbE.eval emptyScope NoContext (environmentOf d) t))) tele
         , bench "glued, unfolded" $ whnf (\d -> sizeOf (NbE.nf scope (definedOf d) t)) tele
         , bench "glued, folded"   $ whnf (\d -> sizeOf (NbE.nf scope (withUnfolding Folded (definedOf d)) t)) tele
         ]

-- | @d0 = 1@ and @dᵢ₊₁ = plus dᵢ dᵢ@ up to @dₖ₊₁@, so that @dᵢ@ unfolds to
-- the numeral @2ⁱ@.
doubling :: Int -> [(String, String)]
doubling k =
  plusDefinition : ("d0", "suc zero")
    : [ ("d" ++ show i, "plus d" ++ show (i - 1) ++ " d" ++ show (i - 1)) | i <- [1 .. k + 1] ]

-- | Check @t ≡ u@ under @'doubling' k@, in the plain environment and glued.
compareConversion :: String -> Int -> String -> String -> Benchmark
compareConversion name k t u =
  withProgram (doubling k) $ \tele scope names ->
    let t' = parseComposed scope names t
        u' = parseComposed scope names u
    in bgroup name
         [ bench "plain" $ whnf (\d -> let values = environmentOf d in convertibleUnder emptyScope NoContext values values t' u') tele
         , bench "glued" $ whnf (\d -> convertible scope (definedOf d) t' u') tele
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
    , bgroup "Conversion"
        [ compareConvertible "mult 16 16 = 256"       (churchMul 16 16) (churchN 256)
        , compareConvertible "2^10 = 1024"            (power 10 2) (churchN 1024)
        , compareConvertible "mult 16 16 /= 255"      (churchMul 16 16) (churchN 255)
        , compareConvertible "mult 16 16 /= 0"        (churchMul 16 16) (churchN 0)
        , compareConvertible "eta, 100 arguments"     (fromString (etaFunction 100)) "\\f. f"
        , compareConvertible "eta, 1000 arguments"    (fromString (etaFunction 1000)) "\\f. f"
        ]
    , bgroup "Conversion: composed vs monolith"
        [ compareComposedConversion "Church mult 16 16 = 256"  (churchMul 16 16) (churchN 256)
        , compareComposedConversion "Church mult 16 16 /= 255" (churchMul 16 16) (churchN 255)
        , compareFullConversion     "natrec mult 16 16 = 256"  (natMul 16 16) (fromString (natural 256))
        , compareFullConversion     "natrec mult 16 16 /= 255" (natMul 16 16) (fromString (natural 255))
        ]
    , bgroup "Conversion: η, lambda-pi vs composed"
        [ bgroup "eta, 1000 arguments"
            [ bench "lambda-pi" $ whnf (uncurry (convertible emptyScope NoContext)) (fromString (etaFunction 1000) :: LambdaPi VoidS, "\\f. f")
            , bench "composed"  $ whnf (uncurry (convertible emptyScope NoContext)) (Composed.fromMonolith (fromString (etaFunction 1000)), Composed.fromMonolith "\\f. f")
            ]
        , bench "pair eta, depth 10 (composed)" $
            whnf (uncurry (convertible emptyScope NoContext)) (Composed.fromMonolith (fromString (etaPair 10)), Composed.fromMonolith "\\p. p")
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
