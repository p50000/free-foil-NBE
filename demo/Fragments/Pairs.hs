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
-- | The fragment of pairs: a pair former, the two projections and @split@,
-- whose pattern binds both components. The rules and the η law of pairs
-- are those of "Pairs", written for any language that contains the
-- fragment:
-- a projection fires on a pair value and is stuck otherwise; @split@ of a
-- pair enters its body with both components in the environment, by position
-- in the pattern, and on anything else it is suspended with its scrutinee
-- evaluated.
module Fragments.Pairs
  ( PairF (..)
  , fstValue
  , sndValue
  ) where

import Control.DeepSeq        (NFData)
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Data.Bifunctor.TH       (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.ZipMatchK.TH       (deriveZipMatchK)
import GHC.Generics            (Generic)

import FreeFoil.NbE            (EtaTerm (..), Value (..), eval, evalNode)
import FreeFoil.NbE.Sum

-- | Pairs: @(t, u)@, @fst t@, @snd t@ and @split t as (x, y) in u@.
data PairF scope term
  = PairF term term
  | FstF term
  | SndF term
  | SplitF term scope
  deriving (Functor, Generic)

deriveBifunctor ''PairF
deriveBifoldable ''PairF
deriveBitraversable ''PairF

deriveZipMatchK ''PairF
instance (NFData scope, NFData term) => NFData (PairF scope term)

instance CoSinkable binder => EvalF binder PairF where
  {-# INLINE evalF #-}
  evalF pos scope env = \case
    FstF p -> fstValue pos (eval scope env p)
    SndF p -> sndValue pos (eval scope env p)
    SplitF p (ScopedAST binder body) ->
      case eval scope env p of
        VNode node | Just (PairF a b) <- prj pos node ->
          case assertDistinct binder of
            Distinct -> eval scope (addSubstPattern env binder [a, b]) body
        p' -> VSuspended env (inj pos (SplitF p' (ScopedAST binder body)))
    node -> evalNode scope env (inj pos node)

  {-# INLINE etaMatchWithF #-}
  etaMatchWithF pos _ term = \case
    PairF a b -> Just (PairF (term a (EtaTerm (const (fstValue pos)))) (term b (EtaTerm (const (sndValue pos)))))
    _ -> Nothing

-- | The first component of a pair value of the fragment; stuck on anything
-- else.
fstValue :: Inj PairF sig -> Value binder sig n -> Value binder sig n
{-# INLINE fstValue #-}
fstValue pos p = case p of
  VNode node | Just (PairF a _) <- prj pos node -> a
  _                                             -> VNode (inj pos (FstF p))

-- | The second component of a pair value of the fragment; stuck on anything
-- else.
sndValue :: Inj PairF sig -> Value binder sig n -> Value binder sig n
{-# INLINE sndValue #-}
sndValue pos p = case p of
  VNode node | Just (PairF _ b) <- prj pos node -> b
  _                                             -> VNode (inj pos (SndF p))
