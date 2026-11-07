{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE LambdaCase #-}
-- | Tests of the dependent types language: the normal forms, conversions and
-- subtypings of the examples in a context of types, and elaboration errors.
module Test.DependentTypes (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv, foldAST)
import Control.Monad.Free.Foil.Annotated (AnnSig (..))
import Data.Bifoldable (bifoldMap)
import Data.Functor.Const (Const (..))

import DependentTypes (Elaborated, Raw, TypedPattern (..), Unfolding (..), convertible, emptyTyping, eval, fullyAnnotated, isSubtype, nf, unannotated, whnf)
import DependentTypes.Elaborate (checksUnder, elaborate, typeIs)
import DependentTypes.Examples

tests :: TestTree
tests =
  testGroup "dependent types"
    [ testGroup "every example reaches its normal form in a context of types"
        [ testCase name $ do
            (term, _) <- elaborated term0 ty
            (normal, _) <- elaborated normal0 ty
            let result = nf emptyScope emptyTyping term
            assertBool (show result) (alphaEquiv emptyScope result normal)
        | (name, Example term0 ty normal0) <- examples
        ]
    , testGroup "every node but a universe carries its type, before and after normalisation"
        [ testCase name $ do
            (term, _) <- elaborated term0 ty
            assertBool (show term) (fullyAnnotated term)
            let result = nf emptyScope emptyTyping term
            assertBool (show result) (fullyAnnotated result)
        | (name, Example term0 ty _) <- examples
        ]
    , testGroup "conversion in a context of types"
        [ testCase name $ do
            (t, _) <- elaborated t0 ty
            (u, _) <- elaborated u0 ty
            convertible emptyScope emptyTyping t u @?= expected
        | (name, Conversion ty t0 u0 expected) <- conversions
        ]
    , testGroup "subtyping in a context of types" $
        [ testCase name $ do
            (a, _) <- elaborated a0 "U 3"
            (b, _) <- elaborated b0 "U 3"
            isSubtype emptyScope emptyTyping (evalType a) (evalType b) @?= expected
        | (name, Subtyping a0 b0 expected) <- subtypings
        ] ++
        [ testCase "the body of a λ, compared invariantly" $ do
            -- Positions other than those of a universe, a Π or a Σ are
            -- compared invariantly, also under a binder.
            (f, _) <- elaborated "\\(x : U 0). U 0" "(x : U 0) -> U 2"
            (g, _) <- elaborated "\\(x : U 0). U 1" "(x : U 0) -> U 2"
            isSubtype emptyScope emptyTyping (evalType f) (evalType g) @?= False
        ]
    , testGroup "the type of a defined name is read off its folded head"
        [ testCase "folded, the declared type" $
            typeIs Folded definitions "f" "T" @?= Right True
        , testCase "folded, not the type the body computes" $
            typeIs Folded definitions "f" "(x : Unit) -> Unit" @?= Right False
        , testCase "unfolded, the type the body computes" $
            typeIs Unfolded definitions "f" "(x : Unit) -> Unit" @?= Right True
        ]
    , testGroup "elaboration rejects"
        [ testCase "a term of another type" $
            rejects "\\(x : Unit). x" "(x : U 0) -> U 0"
        , testCase "an application of a non-function" $
            rejects "tt tt" "Unit"
        , testCase "a projection of a value that is not of a Σ type" $
            rejects "\\(x : Unit). first x" "(x : Unit) -> Unit"
        , testCase "a universe in itself" $
            rejects "U 0" "U 0"
        , testCase "a type of a higher universe as one of a lower" $
            rejects "\\(A : U 1). A" "(A : U 1) -> U 0"
        , testCase "a function on a lower universe as one on a higher" $
            rejects "\\(f : (X : U 0) -> U 0). f" "(f : (X : U 0) -> U 0) -> (X : U 1) -> U 0"
        , testCase "a pair pattern at a type that is not a Σ" $
            rejects "\\((x, y) : Unit). x" "(u : Unit) -> Unit"
        , testCase "refl between sides that are not convertible" $
            rejects "\\(A : U 0). \\(a : A). \\(b : A). refl" "(A : U 0) -> (a : A) -> (b : A) -> Id A a b"
        , testCase "refl against a type that is not an identity type" $
            rejects "refl" "Unit"
        ]
    , testGroup "refl relates a λ over a pair pattern to a λ over a variable"
        [ testCase "the pattern on the left" $
            accepts "\\(A : U 0). refl" ("(A : U 0) -> Id " ++ swapType ++ " (" ++ swapPattern ++ ") (" ++ swapVariable ++ ")")
        , testCase "the pattern on the right" $
            accepts "\\(A : U 0). refl" ("(A : U 0) -> Id " ++ swapType ++ " (" ++ swapVariable ++ ") (" ++ swapPattern ++ ")")
        , testCase "as defined names" $
            checksUnder [("A", "U 0", Nothing), ("swap", swapType, Just swapPattern), ("swap'", swapType, Just swapVariable)] "refl" ("Id " ++ swapType ++ " swap swap'") @?= Right ()
        ]
    , testGroup "the types of a binder are read back under the environment"
        [ testCase "a pair pattern after β" $ do
            (term, _) <- elaborated "(\\(g : (A : U 1) -> (p : (a : A) * A) -> (b : A) * A). g (U 0)) (\\(A : U 1). \\((x, y) : (a : A) * A). (y, x))" "(p : (a : U 0) * U 0) -> (b : U 0) * U 0"
            (sigma, _) <- elaborated "(a : U 0) * U 0" "U 1"
            (u0, _) <- elaborated "U 0" "U 1"
            let result = nf emptyScope emptyTyping term
            case pairTypes result of
              [ty, a] -> do
                assertBool (show ty) (alphaEquiv emptyScope ty (unannotated sigma))
                assertBool (show a) (alphaEquiv emptyScope a (unannotated u0))
              types -> assertFailure ("the types of the pattern of " ++ show result ++ ": " ++ show types)
        , testCase "a binder under the binder of a λ, after β and whnf" $ do
            -- whnf stops at the binder of y, and the binder of x below it
            -- keeps the type A, substituted by U 0.
            (term, _) <- elaborated "(\\(A : U 1). \\(y : U 0). \\(x : A). x) (U 0)" "(y : U 0) -> (x : U 0) -> U 0"
            binderTypes (whnf emptyScope emptyTyping term) @?= ["U 0", "U 0"]
        ]
    ]
  where
    elaborated term ty = either assertFailure pure (elaborate term ty)
    evalType = eval emptyScope emptyTyping identitySubst
    rejects term ty = case elaborate term ty of
      Left _ -> pure ()
      Right (t, _) -> assertFailure ("elaborated to " ++ show t)
    accepts term ty = either assertFailure (const (pure ())) (elaborate term ty)
    swapType = "((p : (a : A) * A) -> (b : A) * A)"
    swapPattern = "\\((x, y) : (a : A) * A). (y, x)"
    swapVariable = "\\(p : (a : A) * A). (second p, first p)"

-- | The types of the pair patterns of the binders at the root of a term, in
-- its scope: the type of each pair and of its first component.
pairTypes :: Elaborated n -> [Raw n]
pairTypes term = types
  where
    Types types = foldAST (\_ -> Types []) (\pat _ -> Types (ofPattern pat)) (\(AnnSig _ node) -> Types (bifoldMap (\(Types ts) -> ts) (const []) node)) term
    ofPattern :: TypedPattern m l -> [Raw m]
    ofPattern = \case
      TypedPair ty (TypedVar _ a) _ -> [unannotated ty, unannotated a]
      _ -> []

newtype Types n = Types [Raw n]

-- | The types of all binders of a term, outermost first, printed.
binderTypes :: Elaborated n -> [String]
binderTypes = getConst . foldAST (\_ -> Const []) (\pat (Const body) -> Const (ofPattern pat ++ body)) (\(AnnSig _ node) -> Const (bifoldMap getConst getConst node))
  where
    ofPattern :: TypedPattern m l -> [String]
    ofPattern = \case
      TypedVar _ ty -> [show ty]
      TypedPair ty l r -> show ty : ofPattern l ++ ofPattern r

-- | A type synonym and a function declared at it.
definitions :: [(String, String, String)]
definitions = [("T", "U 0", "(x : Unit) -> Unit"), ("f", "T", "\\(x : Unit). x")]
