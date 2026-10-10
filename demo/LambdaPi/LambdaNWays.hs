{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Bridge to Weirich's @lambda-n-ways@ benchmark harness, in Karina
-- Tyulebaeva's fork with foil entries. The harness works over an untyped
-- named lambda calculus @LC IdInt@. 'LC' and 'IdInt' mirror the
-- harness's types so that the bridge is testable here; the harness under
-- @bench/lambda-n-ways@ maps them onto the real ones.
module LambdaPi.LambdaNWays
  ( IdInt (..)
  , LC (..)
  , fromLC
  , toLC
  , nbeNf
  , monoNf
  , codegenNf
  , refNf
  , aeq
  ) where

import Control.DeepSeq (NFData)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Generics (Generic)

import Control.Monad.Foil
import Control.Monad.Free.Foil (alphaEquiv)
import qualified LambdaPi as LP
import qualified LambdaPi.Codegen as Codegen
import qualified LambdaPi.Monomorphic as Mono

-- | Integer variable identifiers.
newtype IdInt = IdInt Int
  deriving (Eq, Ord, Show, Generic)

instance NFData IdInt

-- | Untyped named lambda terms.
data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
  deriving (Eq, Show, Generic)

instance NFData v => NFData (LC v)

-- | Convert a closed named term into scope-safe lambda-pi syntax.
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

-- | Convert scope-safe syntax back to a named term, naming variables by their
-- foil identifiers. @Pi@ is outside the untyped fragment and is an error.
toLC :: LP.LambdaPi n -> LC IdInt
toLC = \case
  LP.Var x        -> Var (IdInt (nameId x))
  LP.App f a      -> App (toLC f) (toLC a)
  LP.Lam binder b -> Lam (IdInt (nameId (nameOf binder))) (toLC b)
  LP.Pi _ _ _     -> error "toLC: Pi is outside the untyped lambda fragment"

-- | Normal form by the generic NbE.
nbeNf :: LC IdInt -> LC IdInt
nbeNf = toLC . LP.nfNbe emptyScope . fromLC

-- | Normal form by the monomorphic NbE.
monoNf :: LC IdInt -> LC IdInt
monoNf = toLC . Mono.nfMono emptyScope . fromLC

-- | Normal form by the NbE with a generated value type.
codegenNf :: LC IdInt -> LC IdInt
codegenNf = toLC . Codegen.nfCodegen emptyScope . fromLC

-- | Normal form by the reference substitution normaliser.
refNf :: LC IdInt -> LC IdInt
refNf = toLC . LP.nf emptyScope . fromLC

-- | α-equivalence, through the scope-safe terms.
aeq :: LC IdInt -> LC IdInt -> Bool
aeq a b = alphaEquiv emptyScope (fromLC a) (fromLC b)
