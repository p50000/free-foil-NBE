{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes      #-}
-- | The language composed from fragments: examples on mixed terms, agreement
-- with the standalone languages on embedded terms, properties on random mixed
-- terms, and the shape check of binders in conversion, which only a pattern
-- type with two constructors reaches.
module Test.Fragments (tests) where

import           Control.DeepSeq           (NFData, rnf)
import           Control.Exception         (evaluate)
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import           System.Timeout            (timeout)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil   (alphaEquiv)
import           FreeFoil.NbE.Conversion   (convertible)

import           Fragments.Combined
import qualified LambdaPi
import qualified Naturals
import qualified Naturals.Parser
import qualified Pairs
import qualified Pairs.Parser
import           Test.Agree                (agreesWithin)
import           Test.LambdaPi.Gen         (Closed (..))
import qualified Test.Naturals             as Naturals
import qualified Test.Pairs                as Pairs

tests :: TestTree
tests = testGroup "fragments"
  [ testGroup "examples"
      [ testGroup "closed terms" [ example name t expected | (name, t, expected) <- closedExamples ]
      , testGroup "open terms" [ openExample name t expected | (name, t, expected) <- openExamples ]
      , testGroup "whnf"
          [ openWhnf "keeps a redex under a stuck split"
              (RSplit (RVar "a") "x" "y" (RApp (RLam "z" (RVar "z")) (RVar "x")))
              (RSplit (RVar "a") "x" "y" (RApp (RLam "z" (RVar "z")) (RVar "x")))
          , openWhnf "reduces the zero branch of a stuck recursion, not the suc branch"
              (RNatRec (RVar "a") (RApp (RLam "z" (RVar "z")) RZero) "k" "r" (RApp (RLam "z" (RVar "z")) (RVar "r")))
              (RNatRec (RVar "a") RZero "k" "r" (RApp (RLam "z" (RVar "z")) (RVar "r")))
          ]
      ]
  , testGroup "agrees with the standalone language"
      [ testProperty "lambda-pi, closed terms" propLambdaPi
      , testProperty "pairs, open terms" propPairs
      , testProperty "naturals, closed terms" propNaturalsClosed
      , testProperty "naturals, open terms" propNaturalsOpen
      ]
  , testGroup "mixed terms"
      [ testProperty "nf is idempotent" propIdempotent
      , testProperty "a term is convertible with its normal form" propConvertibleNf
      , testProperty "conversion agrees with alpha-equivalence of normal forms" propConversion
      ]
  , testGroup "binders of different shapes"
      [ testCase "are not convertible" $ do
          assertBool "one name against two" (not (convertible emptyScope oneName twoNames))
          assertBool "two names against one" (not (convertible emptyScope twoNames oneName))
      , testCase "are not alpha-equivalent" $
          assertBool "alphaEquiv" (not (alphaEquiv emptyScope oneName twoNames))
      , testCase "read back as they are" $
          assertBool "nf" (alphaEquiv emptyScope (nf emptyScope twoNames) twoNames)
      ]
  ]

-- * Terms, from a raw syntax with string names

data Raw
  = RVar String
  | RLam String Raw
  | RApp Raw Raw
  | RPair Raw Raw
  | RFst Raw
  | RSnd Raw
  | RSplit Raw String String Raw
  | RZero
  | RSuc Raw
  | RNatRec Raw Raw String String Raw
  deriving (Show)

rnum :: Int -> Raw
rnum k = iterate RSuc RZero !! k

resolve :: Distinct n => Scope n -> Map String (Name n) -> Raw -> Combined n
resolve scope env = \case
  RVar x -> Var (env Map.! x)
  RLam x body -> withFresh scope $ \b ->
    Lam (PatVar b) (resolve (extendScope b scope) (bind x b env) body)
  RApp f a -> App (resolve scope env f) (resolve scope env a)
  RPair a b -> Pair (resolve scope env a) (resolve scope env b)
  RFst p -> Fst (resolve scope env p)
  RSnd p -> Snd (resolve scope env p)
  RSplit p x y body -> withFresh scope $ \bx ->
    let scope' = extendScope bx scope
    in withFresh scope' $ \by ->
         Split (resolve scope env p) (PatPair bx by)
           (resolve (extendScope by scope') (bind y by (bind x bx env)) body)
  RZero -> Zero
  RSuc t -> Suc (resolve scope env t)
  RNatRec n z k r s -> withFresh scope $ \bk ->
    let scope' = extendScope bk scope
    in withFresh scope' $ \br ->
         NatRec (resolve scope env n) (resolve scope env z) (PatPair bk br)
           (resolve (extendScope br scope') (bind r br (bind k bk env)) s)
  where
    bind :: DExt n l => String -> NameBinder n l -> Map String (Name n) -> Map String (Name l)
    bind x b m = Map.insert x (nameOf b) (Map.map sink m)

-- | Free variables of the open examples and the random mixed terms.
freeVars :: [String]
freeVars = ["a", "b"]

withFree :: (forall n. Distinct n => Scope n -> Map String (Name n) -> r) -> r
withFree = Pairs.Parser.withFreeVars emptyScope Map.empty freeVars

-- * Examples

closedExamples :: [(String, Raw, Raw)]
closedExamples =
  [ ( "beta through a pair"
    , RApp (RLam "x" (RPair (RVar "x") (RVar "x"))) RZero
    , RPair RZero RZero )
  , ( "a projection of a function's result"
    , RFst (RApp (RLam "x" (RPair (RSuc (RVar "x")) RZero)) (rnum 2))
    , rnum 3 )
  , ( "recursion on a computed numeral"
    , RNatRec (RApp (RLam "x" (RVar "x")) (rnum 2)) (rnum 3) "k" "r" (RSuc (RVar "r"))
    , rnum 5 )
  , ( "addition through split"
    , RSplit (RPair (rnum 1) (rnum 2)) "x" "y" (RNatRec (RVar "x") (RVar "y") "k" "r" (RSuc (RVar "r")))
    , rnum 3 )
  , ( "a function under natrec"
    , RNatRec (rnum 2) (RLam "f" (RVar "f")) "k" "r" (RApp (RLam "g" (RVar "g")) (RVar "r"))
    , RLam "f" (RVar "f") )
  ]

openExamples :: [(String, Raw, Raw)]
openExamples =
  [ ( "a stuck projection"
    , RFst (RApp (RVar "a") RZero)
    , RFst (RApp (RVar "a") RZero) )
  , ( "beta under a stuck split"
    , RSplit (RVar "a") "x" "y" (RApp (RLam "z" (RVar "z")) (RVar "x"))
    , RSplit (RVar "a") "x" "y" (RVar "x") )
  , ( "a stuck recursion with normal branches"
    , RNatRec (RVar "a") (RApp (RLam "z" (RVar "z")) RZero) "k" "r" (RApp (RLam "z" (RVar "z")) (RVar "r"))
    , RNatRec (RVar "a") RZero "k" "r" (RVar "r") )
  , ( "split of a pair of neutrals"
    , RSplit (RPair (RVar "a") (RVar "b")) "x" "y" (RPair (RVar "y") (RVar "x"))
    , RPair (RVar "b") (RVar "a") )
  ]

example :: String -> Raw -> Raw -> TestTree
example name t expected = testCase name $
  assertBool (show (nf emptyScope term)) (alphaEquiv emptyScope (nf emptyScope term) (resolve emptyScope Map.empty expected))
  where
    term = resolve emptyScope Map.empty t

openExample :: String -> Raw -> Raw -> TestTree
openExample name t expected = testCase name $ withFree $ \scope env ->
  let term = resolve scope env t
  in assertBool (show (nf scope term)) (alphaEquiv scope (nf scope term) (resolve scope env expected))

openWhnf :: String -> Raw -> Raw -> TestTree
openWhnf name t expected = testCase name $ withFree $ \scope env ->
  let term = resolve scope env t
  in assertBool (show (whnf scope term)) (alphaEquiv scope (whnf scope term) (resolve scope env expected))

-- * Agreement with the standalone languages on embedded terms

fromLambdaPi :: LambdaPi.LambdaPi n -> Combined n
fromLambdaPi = \case
  LambdaPi.Var x -> Var x
  LambdaPi.App f a -> App (fromLambdaPi f) (fromLambdaPi a)
  LambdaPi.Lam b body -> Lam (PatVar b) (fromLambdaPi body)
  LambdaPi.Pi dom b cod -> Pi (fromLambdaPi dom) (PatVar b) (fromLambdaPi cod)

fromPairs :: Pairs.Pairs n -> Combined n
fromPairs = \case
  Pairs.Var x -> Var x
  Pairs.Pair a b -> Pair (fromPairs a) (fromPairs b)
  Pairs.Fst p -> Fst (fromPairs p)
  Pairs.Snd p -> Snd (fromPairs p)
  Pairs.Split p x y body -> Split (fromPairs p) (PatPair x y) (fromPairs body)

fromNaturals :: Naturals.Naturals n -> Combined n
fromNaturals = \case
  Naturals.Var x -> Var x
  Naturals.Zero -> Zero
  Naturals.Suc t -> Suc (fromNaturals t)
  Naturals.NatRec n z k r s -> NatRec (fromNaturals n) (fromNaturals z) (PatPair k r) (fromNaturals s)

-- | Lambda-pi terms may diverge, so the comparison has the usual budget.
propLambdaPi :: Closed -> Property
propLambdaPi (Closed t) = ioProperty $
  agreesWithin "the composed nf" (alphaEquiv emptyScope)
    (fromLambdaPi (LambdaPi.nf emptyScope t))
    (nf emptyScope (fromLambdaPi t))

propPairs :: Pairs.OpenTerm -> Bool
propPairs (Pairs.OpenTerm raw) =
  Pairs.Parser.withFreeVars emptyScope Map.empty Pairs.freeVars $ \scope env ->
    let t = Pairs.Parser.resolve scope env raw
    in alphaEquiv scope (fromPairs (Pairs.nf scope t)) (nf scope (fromPairs t))

propNaturalsClosed :: Naturals.ClosedTerm -> Bool
propNaturalsClosed (Naturals.ClosedTerm raw) =
  let t = Naturals.Parser.resolve emptyScope Map.empty raw
  in alphaEquiv emptyScope (fromNaturals (Naturals.nf emptyScope t)) (nf emptyScope (fromNaturals t))

propNaturalsOpen :: Naturals.OpenTerm -> Bool
propNaturalsOpen (Naturals.OpenTerm raw) =
  Naturals.Parser.withFreeVars emptyScope Map.empty Naturals.freeVars $ \scope env ->
    let t = Naturals.Parser.resolve scope env raw
    in alphaEquiv scope (fromNaturals (Naturals.nf scope t)) (nf scope (fromNaturals t))

-- * Random mixed terms

newtype Mixed = Mixed Raw
  deriving (Show)

instance Arbitrary Mixed where
  arbitrary = Mixed <$> sized (genRaw freeVars)

-- | A random term over all three fragments. Binder names are positional, so
-- binders on one spine are distinct.
genRaw :: [String] -> Int -> Gen Raw
genRaw vars n
  | n <= 1 = oneof [RVar <$> elements vars, pure RZero]
  | otherwise =
      frequency
        [ (3, RApp <$> sub <*> sub)
        , (3, RLam x <$> genRaw (x : vars) (n - 1))
        , (2, RPair <$> sub <*> sub)
        , (1, RFst <$> sub)
        , (1, RSnd <$> sub)
        , (2, RSplit <$> sub <*> pure x <*> pure y <*> genRaw (y : x : vars) half)
        , (2, RSuc <$> genRaw vars (n - 1))
        , (2, RNatRec <$> sub <*> sub <*> pure x <*> pure y <*> genRaw (y : x : vars) half)
        ]
  where
    half = n `div` 2
    sub = genRaw vars half
    x = "x" ++ show n
    y = "y" ++ show n

-- | Mixed terms contain functions, so a normal form may not exist: a case is
-- discarded when forcing @x@ does not finish within one second.
budgeted :: NFData a => a -> (a -> Bool) -> IO Property
budgeted x check = do
  done <- timeout 1000000 (evaluate (rnf x))
  pure $ case done of
    Nothing -> property Discard
    Just () -> property (check x)

propIdempotent :: Mixed -> Property
propIdempotent (Mixed raw) = withFree $ \scope env ->
  let v = nf scope (resolve scope env raw)
  in ioProperty $ budgeted v $ \v' -> alphaEquiv scope v' (nf scope v')

propConvertibleNf :: Mixed -> Property
propConvertibleNf (Mixed raw) = withFree $ \scope env ->
  let t = resolve scope env raw
  in ioProperty $ budgeted (nf scope t) $ \v -> convertible scope t v

propConversion :: Mixed -> Mixed -> Property
propConversion (Mixed raw1) (Mixed raw2) = withFree $ \scope env ->
  let t1 = resolve scope env raw1
      t2 = resolve scope env raw2
  in ioProperty $ budgeted (nf scope t1, nf scope t2) $ \(v1, v2) ->
       convertible scope t1 t2 == alphaEquiv scope v1 v2

-- * Binders of different shapes

oneName :: Combined VoidS
oneName = withFresh emptyScope $ \x -> Lam (PatVar x) (Var (nameOf x))

twoNames :: Combined VoidS
twoNames = withFresh emptyScope $ \x ->
  withFresh (extendScope x emptyScope) $ \y ->
    Lam (PatPair x y) (Var (sink (nameOf x)))
