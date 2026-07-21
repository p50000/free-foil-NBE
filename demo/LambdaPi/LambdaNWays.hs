{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Adapter that plugs the generic NbE normaliser into Weirich's
-- @lambda-n-ways@ benchmark harness (Karina Tyulebaeva's free-foil fork).
--
-- The harness works over an /untyped/ named lambda calculus and packages every
-- implementation as a @LambdaImpl@ record with fields
-- @impl_fromLC@ / @impl_toLC@ / @impl_nf@ / @impl_nfi@ / @impl_aeq@ (see
-- @Util.Impl@) over @LC IdInt@ (see @Util.Syntax.Lambda@ / @Util.IdInt@).
--
-- The 'LC' and 'IdInt' types below /mirror/ those harness types so this bridge
-- is self-contained and testable here. To land an actual entry in the harness,
-- drop these mirrors, import the real harness modules, and assemble the
-- functions below into a @LambdaImpl@ registered in the fork's @Suite@ — the
-- foil entries live under @lib/FreeScoped@ and follow exactly this shape (with
-- @impl_nfi = error "unimplemented"@, which we also leave out).
module LambdaPi.LambdaNWays
  ( IdInt (..)
  , LC (..)
  , fromLC
  , toLC
  , nbeNf
  , refNf
  , aeq
  ) where

import Control.DeepSeq (NFData)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Generics (Generic)

import FreeFoil.NbE
  ( S (VoidS), Scope, Name, Distinct, DistinctEvidence (Distinct)
  , alphaEquiv, assertDistinct, emptyScope, extendScope, nameId, nameOf, sink, withFresh
  )
import qualified LambdaPi as LP

-- | Integer variable identifiers (mirrors @Util.IdInt.IdInt@).
newtype IdInt = IdInt Int
  deriving (Eq, Ord, Show, Generic)

instance NFData IdInt

-- | Untyped named lambda terms (mirrors @Util.Syntax.Lambda.LC@).
data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
  deriving (Eq, Show, Generic)

instance NFData v => NFData (LC v)

-- | Convert a (closed) named lambda term into scope-safe lambda-pi syntax.
fromLC :: LC IdInt -> LP.LambdaPi VoidS
fromLC = go emptyScope IntMap.empty
  where
    go :: Distinct n => Scope n -> IntMap (Name n) -> LC IdInt -> LP.LambdaPi n
    go _ env (Var (IdInt i)) =
      maybe (error ("fromLC: free variable " ++ show i)) LP.Var (IntMap.lookup i env)
    go scope env (App f a) =
      LP.App (go scope env f) (go scope env a)
    go scope env (Lam (IdInt i) body) =
      withFresh scope $ \binder ->
        case assertDistinct binder of
          Distinct ->
            let env' = IntMap.insert i (nameOf binder) (fmap sink env)
            in LP.Lam binder (go (extendScope binder scope) env' body)

-- | Convert scope-safe syntax back to a named lambda term. Names come from the
-- foil identifiers. Errors on 'LP.Pi' (outside the untyped fragment the harness
-- exercises).
toLC :: LP.LambdaPi n -> LC IdInt
toLC = \case
  LP.Var x        -> Var (IdInt (nameId x))
  LP.App f a      -> App (toLC f) (toLC a)
  LP.Lam binder b -> Lam (IdInt (nameId (nameOf binder))) (toLC b)
  LP.Pi _ _ _     -> error "toLC: Pi is outside the untyped lambda fragment"

-- | @impl_nf@ via NbE.
nbeNf :: LC IdInt -> LC IdInt
nbeNf = toLC . LP.nfNbe emptyScope . fromLC

-- | @impl_nf@ via the reference substitution normaliser (for cross-checking).
refNf :: LC IdInt -> LC IdInt
refNf = toLC . LP.nf emptyScope . fromLC

-- | @impl_aeq@ via free-foil's alpha-equivalence on the scope-safe terms.
aeq :: LC IdInt -> LC IdInt -> Bool
aeq a b = alphaEquiv emptyScope (fromLC a) (fromLC b)
