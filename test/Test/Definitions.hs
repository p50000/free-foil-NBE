{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
-- | Tests of top-level definitions on lambda-pi: normalising under a
-- telescope agrees with normalising the program with every definition
-- inlined.
module Test.Definitions (tests) where

import           Data.Map.Strict          (Map)
import qualified Data.Map.Strict          as Map
import           System.Timeout           (timeout)

import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil
import           FreeFoil.NbE.Definitions (Definitions (..), nfUnfolded)
import           LambdaPi                 (LambdaPi, nfSubst)
import           LambdaPi.Generated       (FFPattern, TermSig)
import           LambdaPi.Parser          (parseLambdaPi, resolve, withFreeVars)
import           LambdaPi.Syntax.Abs      (Term)
import           LambdaPi.Syntax.Par      (myLexer, pTerm)
import           Test.Agree               (agreesWithin)
import           Test.LambdaPi.Gen        (genTerm)

tests :: TestTree
tests =
  testGroup "definitions (lambda-pi)"
    [ testGroup "examples"
        [ unfoldsTo "a definition uses the earlier ones"
            [ ("two", "\\s. \\z. s (s z)")
            , ("plus", "\\m. \\n. \\s. \\z. m s (n s z)")
            , ("four", "plus two two")
            ]
            "four" "\\s. \\z. s (s (s (s z)))"
        , unfoldsTo "a definition is unfolded under a binder"
            [ ("twice", "\\f. \\x. f (f x)") ]
            "\\y. twice y" "\\y. \\x. y (y x)"
        , unfoldsTo "a later definition shadows an earlier one"
            [ ("k", "\\a. a"), ("k", "\\b. \\c. b") ]
            "k" "\\b. \\c. b"
        , unfoldsTo "an unused definition is not evaluated"
            [ ("omega", "(\\w. w w) (\\w. w w)"), ("id", "\\x. x") ]
            "id" "\\x. x"
        , testCase "definitions may use the free variables of the outer scope" $
            withFreeVars emptyScope Map.empty ["f"] $ \scope env ->
              withDefinitions scope env [("d", raw "f f")] $ \defs scope' env' ->
                alphaEquiv scope
                  (nfUnfolded scope defs (resolve scope' env' (raw "\\x. d")))
                  (resolve scope env (raw "\\x. f f"))
                  @?= True
        ]
    , testProperty "nfUnfolded agrees with nfSubst of the inlined program" propInlined
    ]

-- | Normalising @term@ under the definitions gives @expected@, within a time
-- budget of one second.
unfoldsTo :: TestName -> [(String, String)] -> String -> String -> TestTree
unfoldsTo name definitions term expected =
  testCase name $
    withDefinitions emptyScope Map.empty [ (x, raw t) | (x, t) <- definitions ] $ \defs scope env -> do
      result <- timeout 1000000 $
        pure $! alphaEquiv emptyScope
          (nfUnfolded emptyScope defs (resolve scope env (raw term)))
          (either error id (parseLambdaPi expected))
      result @?= Just True

raw :: String -> Term
raw = either error id . pTerm . myLexer

-- | Resolve a list of raw definitions into a telescope over scope @n@. Each
-- body sees the names defined before it, and a name defined again shadows
-- the earlier one.
withDefinitions ::
  Distinct n =>
  Scope n ->
  Map String (Name n) ->
  [(String, Term)] ->
  (forall l. Distinct l => Definitions FFPattern TermSig n l -> Scope l -> Map String (Name l) -> r) ->
  r
withDefinitions scope0 env0 = go NoDefinitions scope0 env0
  where
    go ::
      Distinct m =>
      Definitions FFPattern TermSig n m ->
      Scope m ->
      Map String (Name m) ->
      [(String, Term)] ->
      (forall l. Distinct l => Definitions FFPattern TermSig n l -> Scope l -> Map String (Name l) -> r) ->
      r
    go defs scope env [] k = k defs scope env
    go defs scope env ((x, body) : rest) k =
      withFresh scope $ \binder ->
        let defs' = Define defs binder (resolve scope env body)
            env' = Map.insert x (nameOf binder) (Map.map sink env)
        in go defs' (extendScope binder scope) env' rest k

-- | Replace every defined name by its body, by substitution.
inline ::
  Distinct n =>
  Scope n ->
  Definitions FFPattern TermSig n l ->
  LambdaPi l ->
  LambdaPi n
inline _ NoDefinitions t = t
inline scope (Define defs x body) t =
  inline scope defs (substitute (scopeOf scope defs) (addSubst identitySubst x body) t)

scopeOf :: Scope n -> Definitions FFPattern TermSig n l -> Scope l
scopeOf scope NoDefinitions        = scope
scopeOf scope (Define defs x _) = extendScope x (scopeOf scope defs)

-- | A random closed program: up to three definitions, each over the names
-- defined before it, and a term over all of them.
data Program = Program [(String, Term)] Term
  deriving (Show)

instance Arbitrary Program where
  arbitrary = sized $ \n -> do
    k <- chooseInt (0, 3)
    let names = [ 'd' : show i | i <- [0 .. k - 1] ]
        size = n `div` (k + 1)
    bodies <- sequence [ genTerm (reverse (take i names)) size | i <- [0 .. k - 1] ]
    term <- genTerm (reverse names) size
    pure (Program (zip names bodies) term)

propInlined :: Program -> Property
propInlined (Program definitions term) =
  withDefinitions emptyScope Map.empty definitions $ \defs scope env ->
    let t = resolve scope env term
    in ioProperty $
         agreesWithin "nfUnfolded" (alphaEquiv emptyScope)
           (nfSubst emptyScope (inline emptyScope defs t))
           (nfUnfolded emptyScope defs t)
