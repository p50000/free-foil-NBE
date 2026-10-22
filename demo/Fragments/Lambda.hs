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
-- | The fragment of functions: lambda, application and the dependent
-- function type. Its one rule is β, as in "LambdaPi", written for any
-- language that contains the fragment and any binder: a suspended lambda is
-- entered under its captured environment extended with the argument, a
-- neutral head rebuilds the application, and @Pi@ falls through to the
-- default. The binder of a lambda is expected to bind one name; applying a
-- lambda whose pattern binds two fails in 'addSubstPattern'.
module Fragments.Lambda
  ( LamF (..)
  ) where

import Control.DeepSeq        (NFData)
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Data.Bifunctor.TH       (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.ZipMatchK.TH       (deriveZipMatchK)
import GHC.Generics            (Generic)

import FreeFoil.NbE            (Value' (..), eliminate, eval, evalNode, vnode)
import FreeFoil.NbE.Sum

-- | Functions: @λx. t@, @t u@ and @Π (x : a). b@.
data LamF scope term
  = LamF scope
  | AppF term term
  | PiF term scope
  deriving (Functor, Generic)

deriveBifunctor ''LamF
deriveBifoldable ''LamF
deriveBitraversable ''LamF

deriveZipMatchK ''LamF
instance (NFData scope, NFData term) => NFData (LamF scope term)

instance CoSinkable binder => EvalF binder LamF where
  {-# INLINE evalF #-}
  evalF pos scope env = \case
    AppF fun arg ->
      let arg' = eval scope env arg
      in eliminate (eval scope env fun) $ \case
           VSuspended env' node
             | Just (LamF (ScopedAST binder body)) <- prj pos node ->
                 case assertDistinct binder of
                   Distinct -> eval scope (addSubstPattern env' binder [arg']) body
           Stuck fun' -> vnode (inj pos (AppF fun' arg'))
    node -> evalNode scope env (inj pos node)
