{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
-- | Tests of top-level definitions. On lambda-pi, normalising in a context
-- of definitions agrees with normalising the program with every definition
-- inlined, and with evaluating it under an environment that maps each
-- defined name to the value of its body. The composed language unfolds its
-- definitions through the rules of its fragments.
module Test.Definitions (tests) where

import           Data.Map.Strict          (Map)
import qualified Data.Map.Strict          as Map
import           System.Timeout           (timeout)

import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Free.Foil
import qualified Fragments.Combined       as Combined
import qualified FreeFoil.NbE             as NbE
import           FreeFoil.NbE.Conversion  (convertible)
import           FreeFoil.NbE.Definitions (Defined, define, noDefinitions)
import           LambdaPi                 (LambdaPi, Value, nfSubst, pattern Lam)
import           LambdaPi.Generated       (FFPattern, TermSig)
import           LambdaPi.Parser          (resolve, withFreeVars)
import           LambdaPi.Syntax.Abs      (Term)
import           LambdaPi.Syntax.Par      (myLexer, pTerm)
import           Test.Agree               (agreesWithin)
import qualified Test.Fragments           as Fragments
import           Test.LambdaPi.Gen        (genTerm)

tests :: TestTree
tests =
  testGroup "definitions"
    [ testGroup "lambda-pi"
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
                    alphaEquiv scope'
                      (NbE.nf scope' (contextOf scope defs) (resolve scope' env' (raw "\\x. d")))
                      (resolve scope' env' (raw "\\x. f f"))
                      @?= True
            , testCase "an undefined free name stays neutral" $
                withFreeVars emptyScope Map.empty ["f"] $ \scope env ->
                  withDefinitions scope env [("d", raw "\\x. x")] $ \defs scope' env' ->
                    alphaEquiv scope'
                      (NbE.nf scope' (contextOf scope defs) (resolve scope' env' (raw "f d")))
                      (resolve scope' env' (raw "f (\\x. x)"))
                      @?= True
            , testCase "a defined name is convertible with what it unfolds to" $
                withDefinitions emptyScope Map.empty
                  [ ("two", raw "\\s. \\z. s (s z)")
                  , ("plus", raw "\\m. \\n. \\s. \\z. m s (n s z)")
                  ] $ \defs scope env ->
                    convertible scope (contextOf emptyScope defs)
                      (resolve scope env (raw "plus two two"))
                      (resolve scope env (raw "\\s. \\z. s (s (s (s z)))"))
                      @?= True
            , testCase "whnf unfolds a defined name at the head" $
                withDefinitions emptyScope Map.empty [("id", raw "\\x. x")] $ \defs scope env ->
                  alphaEquiv scope
                    (NbE.whnf scope (contextOf emptyScope defs) (resolve scope env (raw "id id")))
                    (resolve scope env (raw "\\x. x"))
                    @?= True
            , testCase "whnf keeps a defined name under a binder" $
                withDefinitions emptyScope Map.empty [("id", raw "\\x. x")] $ \defs scope env ->
                  alphaEquiv scope
                    (NbE.whnf scope (contextOf emptyScope defs) (resolve scope env (raw "\\y. id y")))
                    (resolve scope env (raw "\\y. id y"))
                    @?= True
            , testCase "a name bound in a body may have the raw name of the definition" $
                withDefinitions emptyScope Map.empty [("d", raw "\\z. z")] $ \defs scope env -> do
                  -- The body is resolved in the scope before d, so free-foil
                  -- gives z the raw name it then gives d. The bound z must
                  -- not unfold to d.
                  case defs of
                    Definition _ d (Lam z _) -> nameId (nameOf z) @?= nameId (nameOf d)
                    _                        -> assertFailure "the body is not a lambda"
                  let nfIn t = NbE.nf scope (contextOf emptyScope defs) (resolve scope env (raw t))
                  alphaEquiv scope (nfIn "d") (resolve scope env (raw "\\z. z")) @?= True
                  alphaEquiv scope (nfIn "d d") (resolve scope env (raw "\\z. z")) @?= True
            ]
        , testProperty "nf in the context agrees with nfSubst of the inlined program" propInlined
        , testProperty "nf in the context agrees with evaluation under the environment of the definitions" propEnvironment
        , testProperty "conversion in the context agrees with conversion of the inlined terms" propConvertible
        ]
    , testGroup "composed language"
        [ composedExample "definitions from two fragments unfold"
            [ ("two", "suc (suc zero)")
            , ("add", "\\m. \\n. natrec m { zero -> n ; suc (k, r) -> suc r }")
            ]
            "add two two" (Fragments.natural 4)
        , composedExample "a definition applied to free names"
            [ ("swap", "\\p. split p as (x, y) in (y, x)") ]
            "fst (swap (a, b))" "b"
        ]
    ]

-- | Normalising @term@ in the context of the definitions gives @expected@,
-- within a time budget of one second.
unfoldsTo :: TestName -> [(String, String)] -> String -> String -> TestTree
unfoldsTo name definitions term expected =
  testCase name $
    withDefinitions emptyScope Map.empty [ (x, raw t) | (x, t) <- definitions ] $ \defs scope env -> do
      result <- timeout 1000000 $
        pure $! alphaEquiv scope
          (NbE.nf scope (contextOf emptyScope defs) (resolve scope env (raw term)))
          (resolve scope env (raw expected))
      result @?= Just True

raw :: String -> Term
raw = either error id . pTerm . myLexer

-- | The definitions of a program, as syntax: a telescope that extends scope
-- @n@ to scope @l@, the body of each definition in the scope of the names
-- defined before it.
data Telescope n l where
  EmptyTelescope :: Telescope n n
  Definition :: (Distinct m, DExt m l) => Telescope n m -> NameBinder m l -> LambdaPi m -> Telescope n l

-- | Resolve a list of raw definitions into a telescope over scope @n@. Each
-- body sees the names defined before it, and a name defined again shadows
-- the earlier one.
withDefinitions ::
  Distinct n =>
  Scope n ->
  Map String (Name n) ->
  [(String, Term)] ->
  (forall l. Distinct l => Telescope n l -> Scope l -> Map String (Name l) -> r) ->
  r
withDefinitions scope0 env0 = go EmptyTelescope scope0 env0
  where
    go ::
      Distinct m =>
      Telescope n m ->
      Scope m ->
      Map String (Name m) ->
      [(String, Term)] ->
      (forall l. Distinct l => Telescope n l -> Scope l -> Map String (Name l) -> r) ->
      r
    go defs scope env [] k = k defs scope env
    go defs scope env ((x, body) : rest) k =
      withFresh scope $ \binder ->
        let defs' = Definition defs binder (resolve scope env body)
            env' = Map.insert x (nameOf binder) (Map.map sink env)
        in go defs' (extendScope binder scope) env' rest k

-- | The context of a telescope: its definitions, made in turn.
contextOf :: Distinct n => Scope n -> Telescope n l -> Defined FFPattern TermSig l
contextOf _ EmptyTelescope = noDefinitions
contextOf scope (Definition defs x body) = define (scopeOf scope defs) x body (contextOf scope defs)

-- | The scope of a telescope extends the scope it starts from.
withTelescopeExt :: Distinct n => Telescope n l -> (DExt n l => r) -> r
withTelescopeExt EmptyTelescope k = k
withTelescopeExt (Definition defs _ _) k = withTelescopeExt defs k

-- | Replace every defined name by its body, by substitution.
inline ::
  Distinct n =>
  Scope n ->
  Telescope n l ->
  LambdaPi l ->
  LambdaPi n
inline _ EmptyTelescope t = t
inline scope (Definition defs x body) t =
  inline scope defs (substitute (scopeOf scope defs) (addSubst identitySubst x body) t)

scopeOf :: Scope n -> Telescope n l -> Scope l
scopeOf scope EmptyTelescope = scope
scopeOf scope (Definition defs x _) = extendScope x (scopeOf scope defs)

-- | The environment of a telescope: each defined name maps to the value of
-- its body, and the names of @n@ to themselves.
environmentOf :: Distinct n => Scope n -> Telescope n l -> Substitution Value l n
environmentOf _ EmptyTelescope = identitySubst
environmentOf scope (Definition defs x body) =
  let env = environmentOf scope defs
  in addSubst env x (NbE.eval scope NbE.NoContext env body)

-- | The normal form of a term with every definition unfolded through the
-- environment: the result is a term over the outer scope.
nfEnvironment :: (Distinct n, Distinct l) => Scope n -> Telescope n l -> LambdaPi l -> LambdaPi n
nfEnvironment scope defs = NbE.quote scope NbE.NoContext . NbE.eval scope NbE.NoContext (environmentOf scope defs)

-- | A random program over two free variables: up to three definitions, each
-- over the names defined before it, and two terms over all of them, the
-- second equal to the first a third of the time.
data Program = Program [(String, Term)] Term Term
  deriving (Show)

freeNames :: [String]
freeNames = ["f", "g"]

instance Arbitrary Program where
  arbitrary = sized $ \n -> do
    k <- chooseInt (0, 3)
    let names = [ 'd' : show i | i <- [0 .. k - 1] ]
        size = n `div` (k + 1)
    bodies <- sequence [ genTerm (reverse (take i names) ++ freeNames) size | i <- [0 .. k - 1] ]
    term <- genTerm (reverse names ++ freeNames) size
    other <- frequency [ (1, pure term), (2, genTerm (reverse names ++ freeNames) size) ]
    pure (Program (zip names bodies) term other)

-- | A normaliser of the program's term in the scope of its definitions,
-- given the outer scope.
type Normaliser = forall n l. (Distinct n, Distinct l) => Scope n -> Telescope n l -> LambdaPi l -> LambdaPi l

-- | Normalising in the context agrees with a reference normaliser up to α.
agreesWith :: String -> Normaliser -> Program -> Property
agreesWith name reference (Program definitions term _) =
  withFreeVars emptyScope Map.empty freeNames $ \scope0 env0 ->
    withDefinitions scope0 env0 definitions $ \defs scope env ->
      let t = resolve scope env term
      in ioProperty $
           agreesWithin name (alphaEquiv scope)
             (reference scope0 defs t)
             (NbE.nf scope (contextOf scope0 defs) t)

propInlined :: Program -> Property
propInlined = agreesWith "nf in the context" $ \scope defs t ->
  withTelescopeExt defs (sink (nfSubst scope (inline scope defs t)))

propEnvironment :: Program -> Property
propEnvironment = agreesWith "nf in the context" $ \scope defs t ->
  withTelescopeExt defs (sink (nfEnvironment scope defs t))

propConvertible :: Program -> Property
propConvertible (Program definitions term other) =
  withFreeVars emptyScope Map.empty freeNames $ \scope0 env0 ->
    withDefinitions scope0 env0 definitions $ \defs scope env ->
      let t = resolve scope env term
          u = resolve scope env other
      in ioProperty $
           agreesWithin "conversion in the context" (==)
             (convertible scope0 NbE.NoContext (inline scope0 defs t) (inline scope0 defs u))
             (convertible scope (contextOf scope0 defs) t u)

-- | Normalising @term@ in a context of definitions of the composed language
-- gives @expected@. The terms may use the free variables of
-- 'Fragments.withFree'.
composedExample :: TestName -> [(String, String)] -> String -> String -> TestTree
composedExample name definitions term expected =
  testCase name $ Fragments.withFree $ \scope0 env0 ->
    withDefined scope0 env0 definitions $ \ctx scope env ->
      alphaEquiv scope
        (NbE.nf scope ctx (Fragments.parseIn scope env term))
        (Fragments.parseIn scope env expected)
        @?= True

-- | A context of definitions of the composed language over scope @n@, each
-- body parsed in the scope of the names defined before it.
withDefined ::
  Distinct n =>
  Scope n ->
  Map String (Name n) ->
  [(String, String)] ->
  (forall l. Distinct l => Defined Combined.Pat Combined.Sig l -> Scope l -> Map String (Name l) -> r) ->
  r
withDefined scope0 env0 = go noDefinitions scope0 env0
  where
    go ::
      Distinct m =>
      Defined Combined.Pat Combined.Sig m ->
      Scope m ->
      Map String (Name m) ->
      [(String, String)] ->
      (forall l. Distinct l => Defined Combined.Pat Combined.Sig l -> Scope l -> Map String (Name l) -> r) ->
      r
    go ctx scope env [] k = k ctx scope env
    go ctx scope env ((x, body) : rest) k =
      withFresh scope $ \binder ->
        let ctx' = define scope binder (Fragments.parseIn scope env body) ctx
            env' = Map.insert x (nameOf binder) (Map.map sink env)
        in go ctx' (extendScope binder scope) env' rest k
