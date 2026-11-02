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
-- | Readback of refined values, with a context that knows which free names
-- are functions and η-expands them, as a language with types does. The
-- expansion goes through an environment, which @whnf@ substitutes into a
-- frozen body. The functions refine in a language of their own and as a
-- fragment beside pairs, which refines through the sum, also annotated.
module Test.Refinement (tests) where

import Data.Bifoldable          (Bifoldable)
import Data.Bifunctor           (Bifunctor)
import Data.Bifunctor.Sum       (Sum (..))
import Data.Maybe               (fromMaybe)
import Data.ZipMatchK           (ZipMatchFoldK, ZipMatchK (..))
import Data.ZipMatchK.Bifunctor ()

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil (AST (..), ScopedAST (..), alphaEquiv)
import Control.Monad.Free.Foil.Annotated (AnnSig)

import qualified FreeFoil.NbE    as NbE
import FreeFoil.NbE             (HasHeads)
import FreeFoil.NbE.Annotated   (Annotation (..), ignoring)
import FreeFoil.NbE.Sum         (EvalF (..), Inj (..), inR, root)

import Fragments.Lambda         (LamF (..))
import Fragments.Pairs          (PairF)
import Fragments.Pattern        (Pat (..))

-- | The free names of function type.
newtype Functions n = Functions [Name n]

instance Sinkable Functions where
  sinkabilityProof rename (Functions xs) = Functions (map rename xs)

instance NbE.HasDefinitions Functions Pat sig where
  contextDefinition _ _ = NbE.VVar

-- | Functions on their own: a free name of function type is η-expanded to
-- @λy. f y@, with @f@ bound to it in the environment.
instance NbE.Eval Functions Pat LamF where
  evalSig = evalF root
  refineVar scope ctx x = fromMaybe (NbE.VVar x) (expandFunction root scope ctx x)

-- | Functions as a fragment that refines: the rules of 'LamF', and the same
-- η-expansion.
newtype FunF scope term = FunF (LamF scope term)
  deriving newtype (Functor, Bifunctor, Bifoldable, HasHeads)

deriving newtype instance ZipMatchK FunF
deriving newtype instance ZipMatchFoldK FunF

lamAt :: Inj FunF sig -> Inj LamF sig
lamAt (Inj i p) = Inj (i . FunF) (fmap (\(FunF node) -> node) . p)

instance EvalF Functions Pat FunF where
  evalF pos scope ctx env (FunF node) = evalF (lamAt pos) scope ctx env node
  etaMatchWithF pos scoped term (FunF node) = FunF <$> etaMatchWithF (lamAt pos) scoped term node
  refineVarF pos = expandFunction (lamAt pos)

expandFunction :: Distinct n => Inj LamF sig -> Scope n -> Functions n -> Name n -> Maybe (NbE.Value Pat sig n)
expandFunction pos scope (Functions fs) x
  | x `elem` fs = Just $ withFresh scope $ \f ->
      withFresh (extendScope f scope) $ \y ->
        NbE.VSuspended (addSubst identitySubst f (NbE.VVar x)) (lamNode pos y (sink (nameOf f)))
  | otherwise = Nothing

-- | @λy. f y@ at a position.
lamNode :: Inj LamF sig -> NameBinder n l -> Name l -> sig (ScopedAST Pat sig n) term
lamNode pos y f = inj pos (LamF (ScopedAST (PatVar y) (Node (inj pos (AppF (Var f) (Var (nameOf y)))))))

-- | An annotation with nothing in it.
data Blank term = Blank
  deriving Functor

instance Annotation Blank where
  blank = Blank

instance ZipMatchK Blank where
  zipMatchWithK _ Blank _ = Just Blank

tests :: TestTree
tests = testGroup "refinement"
  [ testGroup "a language of its own" (expandsOnce root)
  , testGroup "a fragment right of pairs" (expandsOnce (lamAt (inR root) :: Inj LamF (Sum PairF FunF)))
  , testGroup "a fragment of an annotated language" (expandsOnce (lamAt (inR ignoring) :: Inj LamF (AnnSig Blank (Sum PairF FunF))))
  ]

-- | @nf@ and @whnf@ η-expand a free function @f@ to @λy. f y@, once.
expandsOnce :: (NbE.Eval Functions Pat sig, ZipMatchK sig) => Inj LamF sig -> [TestTree]
expandsOnce pos = withFresh emptyScope $ \f ->
  let scope = extendScope f emptyScope
      ctx = Functions [nameOf f]
      expanded = withFresh scope $ \y -> Node (lamNode pos y (sink (nameOf f)))
  in [ testCase "nf η-expands a function once" $
         assertBool "λy. f y" (alphaEquiv scope (NbE.nf scope ctx (Var (nameOf f))) expanded)
     , testCase "whnf η-expands a function once" $
         assertBool "λy. f y" (alphaEquiv scope (NbE.whnf scope ctx (Var (nameOf f))) expanded)
     ]
