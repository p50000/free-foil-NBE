{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeFamilies        #-}
-- The Eval instance for the typed annotation is an orphan on purpose: it is
-- this test's language.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Evaluation of annotated terms: the composed language with a position at
-- every node, which evaluation ignores. Normal forms, weak-head normal forms
-- and conversion agree with the unannotated language on examples and on
-- random mixed terms. Two annotations of one term are convertible. A normal
-- form is annotated blank, and a body that @whnf@ freezes keeps its
-- annotations.
module Test.Annotated (tests) where

import qualified Data.Map.Strict as Map
import Data.Bifoldable (bifoldMap)
import Data.Maybe (isJust, isNothing)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Control.Monad.Free.Foil.Annotated (AnnSig (..))
import Data.ZipMatchK (ZipMatchFoldK (..), ZipMatchK (..))
import Data.ZipMatchK.Bifunctor ()

import Data.Bifunctor.Sum (Sum (..))
import Fragments.Combined (Combined, Pat, Sig, nf, whnf)
import Fragments.Lambda (LamF (..))
import FreeFoil.NbE (Eval (..), NoContext, evalNode)
import qualified FreeFoil.NbE as NbE
import FreeFoil.NbE.Annotated
import FreeFoil.NbE.Conversion (convertible)
import FreeFoil.NbE.Definitions (Defined, define, noDefinitions)
import FreeFoil.NbE.Sum (EvalF (..))
import Test.Fragments (Mixed (..), budgeted, parseIn, resolve, withFree)

-- | A position, which ignores the term. Matching ignores positions.
newtype Loc term = Loc (Maybe Int)
  deriving (Show, Functor, Foldable, Traversable)

instance Annotation Loc where
  blank = Loc Nothing

instance ZipMatchK Loc where
  zipMatchWithK _ (Loc l) _ = Just (Loc l)

instance ZipMatchFoldK Loc where
  zipMatchFoldK _ _ _ = Just mempty

type Annotated n = AST Pat (AnnSig Loc Sig) n

-- | Every node annotated with the same position.
annotatedAt :: Int -> Combined n -> Annotated n
annotatedAt k = hoistAST (AnnSig (Loc (Just k)))

-- | An annotation that holds a term, as a type annotation does. Matching
-- ignores it.
newtype Typed term = Typed (Maybe term)
  deriving (Show, Functor, Foldable, Traversable)

instance Annotation Typed where
  blank = Typed Nothing

instance ZipMatchK Typed where
  zipMatchWithK _ _ _ = Just (Typed Nothing)

instance ZipMatchFoldK Typed where
  zipMatchFoldK _ _ _ = Just mempty

type TypedTerm n = AST Pat (AnnSig Typed Sig) n

-- | The rules of the combined language on terms annotated with a term. A λ
-- that evaluation freezes keeps its annotation, as it does in a language
-- whose annotation is the type; the instance of "FreeFoil.NbE.Annotated"
-- blanks it instead.
instance Eval NoContext Pat (AnnSig Typed Sig) where
  evalSig scope ctx env (AnnSig ann node) = case node of
    L2 (LamF _) -> evalNode scope ctx env (AnnSig ann node)
    _           -> evalF ignoring scope ctx env node
  etaMatchWith scoped term (AnnSig _ node) = AnnSig blank <$> etaMatchWithF ignoring scoped term node
  extendScopedWith scoped term (AnnSig ann node) = AnnSig (fmap term ann) (extendScopedWithF ignoring scoped term node)

-- | A term annotated blank, except for its root, which holds the given term.
typedAs :: Combined n -> Combined n -> TypedTerm n
typedAs ann term = case hoistAST (AnnSig blank) term of
  Node (AnnSig _ node) -> Node (AnnSig (Typed (Just (hoistAST (AnnSig blank) ann))) node)
  var                  -> var

-- | The annotations of a term, outermost first.
annotations :: Annotated n -> [Maybe Int]
annotations = \case
  Var _ -> []
  Node (AnnSig (Loc a) node) ->
    a : bifoldMap (\(ScopedAST _ body) -> annotations body) annotations node

nfAnnotated :: Distinct n => Scope n -> Annotated n -> Annotated n
nfAnnotated scope = NbE.nf scope NbE.NoContext

whnfAnnotated :: Distinct n => Scope n -> Annotated n -> Annotated n
whnfAnnotated scope = NbE.whnf scope NbE.NoContext

-- | Contexts of definitions over the annotated and the plain signature.
noAnnotatedDefinitions :: Defined Pat (AnnSig Loc Sig) n
noAnnotatedDefinitions = noDefinitions

noPlainDefinitions :: Defined Pat Sig n
noPlainDefinitions = noDefinitions

tests :: TestTree
tests =
  testGroup "annotations"
    [ testGroup "nf agrees with the unannotated language"
        [ testCase t $
            let term = parseIn emptyScope Map.empty t
            in alphaEquiv emptyScope (unannotated (nfAnnotated emptyScope (annotatedAt 1 term))) (nf emptyScope term) @?= True
        | t <- closedExamples
        ]
    , testGroup "nf agrees on open terms"
        [ testCase t $ withFree $ \scope env ->
            let term = parseIn scope env t
            in alphaEquiv scope (unannotated (nfAnnotated scope (annotatedAt 1 term))) (nf scope term) @?= True
        | t <- openExamples
        ]
    , testGroup "annotations on results"
        [ testCase "a normal form is annotated blank" $
            let term = parseIn emptyScope Map.empty "(\\x. (x, x)) zero"
            in all isNothing (annotations (nfAnnotated emptyScope (annotatedAt 7 term))) @?= True
        , testCase "a body that whnf freezes keeps its annotations" $
            let term = parseIn emptyScope Map.empty "\\x. (\\y. y) x"
            in case annotations (whnfAnnotated emptyScope (annotatedAt 7 term)) of
                 Nothing : rest -> any isJust rest @?= True
                 other          -> assertFailure ("the lambda is not blank: " ++ show other)
        , testCase "the term inside a kept annotation is normalised" $
            let closed = parseIn emptyScope Map.empty
                term = typedAs (closed "fst (zero, zero)") (closed "\\x. x")
            in case NbE.nf emptyScope NbE.NoContext term of
                 Node (AnnSig (Typed (Just ann)) _) ->
                   alphaEquiv emptyScope (unannotated ann) (closed "zero") @?= True
                 Node (AnnSig (Typed Nothing) _) -> assertFailure "the lambda's annotation is blank"
                 Var _ -> assertFailure "the lambda is a variable"
        ]
    , testGroup "definitions"
        [ testCase "a definition unfolds through annotations" $ withFree $ \scope env ->
            withFresh scope $ \d ->
              let body = parseIn scope env "\\x. (x, x)"
                  scope' = extendScope d scope
                  env' = Map.insert "d" (nameOf d) (Map.map sink env)
                  term = parseIn scope' env' "d a"
                  annotated = define scope d (annotatedAt 1 body) noAnnotatedDefinitions
                  plain = define scope d body noPlainDefinitions
              in alphaEquiv scope' (unannotated (NbE.nf scope' annotated (annotatedAt 2 term))) (NbE.nf scope' plain term) @?= True
        ]
    , testGroup "conversion"
        [ testCase "η through an annotation" $
            let closed = parseIn emptyScope Map.empty
            in convertible emptyScope NbE.NoContext (annotatedAt 1 (closed "\\f. \\x. f x")) (annotatedAt 2 (closed "\\f. f")) @?= True
        , testProperty "agrees with the unannotated language" propConv
        , testProperty "two annotations of one term are convertible" propBlind
        ]
    , testGroup "properties"
        [ testProperty "nf agrees with the unannotated language" propNf
        , testProperty "whnf agrees with the unannotated language" propWhnf
        ]
    ]

closedExamples :: [String]
closedExamples =
  [ "(\\x. (x, x)) zero"
  , "fst ((\\x. (suc x, zero)) (suc (suc zero)))"
  , "natrec (suc (suc zero)) { zero -> \\f. f ; suc (k, r) -> (\\g. g) r }"
  , "split (suc zero, zero) as (x, y) in natrec x { zero -> y ; suc (k, r) -> suc r }"
  ]

openExamples :: [String]
openExamples =
  [ "fst (a zero)"
  , "split a as (x, y) in (\\z. z) x"
  , "natrec a { zero -> (\\z. z) zero ; suc (k, r) -> (\\z. z) r }"
  , "(\\z. z) a b"
  ]

propNf :: Mixed -> Property
propNf (Mixed raw) = withFree $ \scope env ->
  let t = resolve scope env raw
  in ioProperty $ budgeted (nf scope t) $ \v ->
       alphaEquiv scope (unannotated (nfAnnotated scope (annotatedAt 1 t))) v

propWhnf :: Mixed -> Property
propWhnf (Mixed raw) = withFree $ \scope env ->
  let t = resolve scope env raw
  in ioProperty $ budgeted (whnf scope t) $ \v ->
       alphaEquiv scope (unannotated (whnfAnnotated scope (annotatedAt 1 t))) v

propConv :: Mixed -> Mixed -> Property
propConv (Mixed raw1) (Mixed raw2) = withFree $ \scope env ->
  let t1 = resolve scope env raw1
      t2 = resolve scope env raw2
  in ioProperty $ budgeted (nf scope t1, nf scope t2) $ \_ ->
       convertible scope NbE.NoContext (annotatedAt 1 t1) (annotatedAt 2 t2) == convertible scope NbE.NoContext t1 t2

propBlind :: Mixed -> Property
propBlind (Mixed raw) = withFree $ \scope env ->
  let t = resolve scope env raw
  in ioProperty $ budgeted (nf scope t) $ \_ ->
       convertible scope NbE.NoContext (annotatedAt 1 t) (annotatedAt 2 t)
