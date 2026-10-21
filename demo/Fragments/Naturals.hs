{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
-- | The fragment of natural numbers: @zero@, @suc@ and primitive recursion,
-- whose @suc@ branch binds the predecessor and the recursive result with one
-- pattern. The rule is that of Renata Shakirova's "Naturals", written for any
-- language that contains the fragment: recursion on the value of the
-- scrutinee with a stuck case for a neutral one, after Abel ("Normalization
-- by Evaluation: Dependent Types and Impredicativity", 2013, Figure 3.2),
-- except that the recursive result is a thunk in the environment, computed
-- only if the branch uses it and shared by every use.
module Fragments.Naturals
  ( NatF (..)
  ) where

import Control.DeepSeq        (NFData)
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Data.Bifunctor.TH       (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.ZipMatchK          (ZipMatchK)
import Generics.Kind.TH        (deriveGenericK)
import GHC.Generics            (Generic)

import FreeFoil.NbE            (Value (..), eval, evalNode)
import FreeFoil.NbE.Sum

-- | Naturals: @zero@, @suc t@ and @natrec n { zero -> z ; suc k, r -> s }@.
data NatF scope term
  = ZeroF
  | SucF term
  | NatRecF term term scope
  deriving (Functor, Generic)

deriveBifunctor ''NatF
deriveBifoldable ''NatF
deriveBitraversable ''NatF
deriveGenericK ''NatF

instance ZipMatchK NatF
instance (NFData scope, NFData term) => NFData (NatF scope term)

instance CoSinkable binder => EvalF binder NatF where
  {-# INLINE evalF #-}
  evalF pos scope env = \case
    NatRecF n z (ScopedAST binder s) ->
      case assertDistinct binder of
        Distinct ->
          let zeroCase = eval scope env z
              recurse m = case m of
                VNode node
                  | Just ZeroF <- prj pos node -> zeroCase
                  | Just (SucF p) <- prj pos node ->
                      eval scope (addSubstPattern env binder [p, recurse p]) s
                m' -> VSuspended env (inj pos (NatRecF m' zeroCase (ScopedAST binder s)))
          in recurse (eval scope env n)
    node -> evalNode (eval scope) env (inj pos node)
