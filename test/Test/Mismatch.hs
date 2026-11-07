{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
-- | Conversion with a context that makes free names equal, as the context
-- of a type theory with an interval makes points equal under its assumed
-- equations: two values that conversion finds different are equal when the
-- language's 'NbE.relateMismatch' says so. The functions relate in a
-- language of their own and as a fragment beside pairs, which relates
-- through the sum.
module Test.Mismatch (tests) where

import Data.Bifoldable          (Bifoldable)
import Data.Bifunctor           (Bifunctor)
import Data.Bifunctor.Sum       (Sum (..))
import Data.ZipMatchK           (ZipMatchFoldK, ZipMatchK (..))
import Data.ZipMatchK.Bifunctor ()

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil  (AST (..), ScopedAST (..))

import qualified FreeFoil.NbE    as NbE
import FreeFoil.NbE             (HasHeads)
import FreeFoil.NbE.Conversion  (convertible)
import FreeFoil.NbE.Sum         (EvalF (..), Inj (..), inR, root)

import Fragments.Lambda         (LamF (..))
import Fragments.Pairs          (PairF)
import Fragments.Pattern        (Pat (..))

-- | The equations between free names that the context assumes.
newtype Equations n = Equations [(Name n, Name n)]

instance Sinkable Equations where
  sinkabilityProof rename (Equations eqs) = Equations [ (rename x, rename y) | (x, y) <- eqs ]

instance NbE.HasDefinitions Equations Pat sig where
  contextDefinition _ _ = NbE.vvar

-- | Two variables are equal when the context assumes they are.
assumedEqual :: Equations n -> NbE.Value Pat sig n -> NbE.Value Pat sig n -> Bool
assumedEqual (Equations eqs) l r = case (NbE.force l, NbE.force r) of
  (NbE.VVar x, NbE.VVar y) -> (x, y) `elem` eqs || (y, x) `elem` eqs
  _                        -> False

-- | Functions on their own.
instance NbE.Eval Equations Pat LamF where
  evalSig = evalF root
  relateMismatch _ ctx = assumedEqual ctx

-- | Functions as a fragment that relates variables.
newtype EqF scope term = EqF (LamF scope term)
  deriving newtype (Functor, Bifunctor, Bifoldable, HasHeads)

deriving newtype instance ZipMatchK EqF
deriving newtype instance ZipMatchFoldK EqF

lamAt :: Inj EqF sig -> Inj LamF sig
lamAt (Inj i p) = Inj (i . EqF) (fmap (\(EqF node) -> node) . p)

instance EvalF Equations Pat EqF where
  evalF pos scope ctx env (EqF node) = evalF (lamAt pos) scope ctx env node
  etaMatchWithF pos scoped term (EqF node) = EqF <$> etaMatchWithF (lamAt pos) scoped term node
  relateMismatchF _ _ ctx = assumedEqual ctx

tests :: TestTree
tests = testGroup "related by the context"
  [ testGroup "a language of its own" (relates root)
  , testGroup "a fragment right of pairs" (relates (lamAt (inR root) :: Inj LamF (Sum PairF EqF)))
  ]

-- | @g a@ at a position.
appAt :: Inj LamF sig -> Name n -> Name n -> AST Pat sig n
appAt pos g a = Node (inj pos (AppF (Var g) (Var a)))

-- | @λw. body@ at a position.
lamAt' :: Inj LamF sig -> NameBinder n l -> AST Pat sig l -> AST Pat sig n
lamAt' pos w body = Node (inj pos (LamF (ScopedAST (PatVar w) body)))

-- | With @x = y@ assumed, @f x@ and @f y@ are convertible, also under a
-- binder; @f x@ and @f z@ are not, nor are @f x@ and @f y@ without the
-- equation.
relates :: NbE.Eval Equations Pat sig => Inj LamF sig -> [TestTree]
relates pos =
  withFresh emptyScope $ \f ->
  withFresh (extendScope f emptyScope) $ \x ->
  withFresh (extendScope x (extendScope f emptyScope)) $ \y ->
  withFresh (extendScope y (extendScope x (extendScope f emptyScope))) $ \z ->
    let scope = extendScope z (extendScope y (extendScope x (extendScope f emptyScope)))
        f' = sink (nameOf f)
        x' = sink (nameOf x)
        y' = sink (nameOf y)
        z' = nameOf z
        app = appAt pos
        assumed = Equations [(x', y')]
        -- λw. f x against λw. f y
        under a b = withFresh scope $ \w ->
          ( lamAt' pos w (appAt pos (sink f') (sink a))
          , lamAt' pos w (appAt pos (sink f') (sink b)) )
    in [ testCase "an assumed equation makes f x and f y convertible" $
           convertible scope assumed (app f' x') (app f' y') @?= True
       , testCase "it holds under a binder" $
           uncurry (convertible scope assumed) (under x' y') @?= True
       , testCase "f x and f z stay different" $
           convertible scope assumed (app f' x') (app f' z') @?= False
       , testCase "without the equation f x and f y are different" $
           convertible scope (Equations []) (app f' x') (app f' y') @?= False
       ]
