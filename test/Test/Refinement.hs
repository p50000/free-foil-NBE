{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
-- | Readback of refined values: the λ fragment with a context that knows
-- which free names are functions and η-expands them, as a language with
-- types does. The expansion goes through an environment, which @whnf@
-- substitutes into a frozen body.
module Test.Refinement (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Foil
import Control.Monad.Free.Foil (AST (..), ScopedAST (..), alphaEquiv)

import qualified FreeFoil.NbE    as NbE
import FreeFoil.NbE.Sum         (EvalF (..), root)

import Fragments.Lambda         (LamF (..))
import Fragments.Pattern        (Pat (..))

-- | The free names of function type.
newtype Functions n = Functions [Name n]

instance Sinkable Functions where
  sinkabilityProof rename (Functions xs) = Functions (map rename xs)

-- | A free name of function type is η-expanded to @λy. f y@, with @f@
-- bound to it in the environment.
instance NbE.Eval Functions Pat LamF where
  definition _ _ = NbE.VVar
  evalSig = evalF root
  refineVar scope (Functions fs) x
    | x `elem` fs = etaExpand scope x
    | otherwise   = NbE.VVar x

etaExpand :: Distinct n => Scope n -> Name n -> NbE.Value Pat LamF n
etaExpand scope x = withFresh scope $ \f ->
  let scopeF = extendScope f scope
  in withFresh scopeF $ \y ->
    NbE.VSuspended (addSubst identitySubst f (NbE.VVar x))
      (LamF (ScopedAST (PatVar y) (Node (AppF (Var (sink (nameOf f))) (Var (nameOf y))))))

type Term n = AST Pat LamF n

tests :: TestTree
tests = withFresh emptyScope $ \f ->
  let scope = extendScope f emptyScope
      ctx = Functions [nameOf f]
      expanded = lam scope (\_ y -> Node (AppF (Var (sink (nameOf f))) (Var y)))
  in testGroup "refinement"
    [ testCase "nf η-expands a function once" $
        assertBool "λy. f y" (alphaEquiv scope (NbE.nf scope ctx (Var (nameOf f))) expanded)
    , testCase "whnf η-expands a function once" $
        assertBool "λy. f y" (alphaEquiv scope (NbE.whnf scope ctx (Var (nameOf f))) expanded)
    ]

lam :: Distinct n => Scope n -> (forall l. DExt n l => Scope l -> Name l -> Term l) -> Term n
lam scope body = withFresh scope $ \x ->
  Node (LamF (ScopedAST (PatVar x) (body (extendScope x scope) (nameOf x))))
