{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Booleans with @if@: a second object language, without binders, showing
-- that the core is generic in the signature. The language is this signature
-- plus one 'Eval' instance; evaluation and normalisation are inherited.
-- Example terms are in "Booleans.Examples".
module Booleans
  ( BoolSig (..)
  , BoolTm
  , pattern TT
  , pattern FF
  , pattern If
  , nf
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Data.Bifunctor (bimap)
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.ZipMatchK.TH (deriveZipMatchK)

import FreeFoil.NbE (Eval (evalSig), HasDefinitions, HasHeads (..), Value' (Stuck, VNode), eliminate, eval, evalNode, vnode)
import qualified FreeFoil.NbE as NbE

-- | Two introduction forms and one eliminator; no scoped positions.
data BoolSig scope term
  = TrueSig
  | FalseSig
  | IfSig term term term
  deriving (Functor)

deriveBifunctor ''BoolSig
deriveBifoldable ''BoolSig
deriveBitraversable ''BoolSig

-- | Node comparison for 'alphaEquiv'; the generic instance suffices here.
deriveZipMatchK ''BoolSig

-- | Boolean terms. The binder type is never used.
type BoolTm = AST NameBinder BoolSig

-- | @true@.
pattern TT :: BoolTm n
pattern TT = Node TrueSig

-- | @false@.
pattern FF :: BoolTm n
pattern FF = Node FalseSig

-- | @if c then t else f@.
pattern If :: BoolTm n -> BoolTm n -> BoolTm n -> BoolTm n
pattern If c t f = Node (IfSig c t f)

-- | The heads: the condition of @if@.
instance HasHeads BoolSig where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    IfSig cond t f -> IfSig (hd cond) (other t) (other f)
    node           -> bimap id other node

-- | The one elimination rule: a canonical condition selects a branch, a
-- neutral condition leaves the @if@ stuck.
instance (Sinkable ctx, HasDefinitions ctx NameBinder BoolSig) => Eval ctx NameBinder BoolSig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env = \case
    IfSig cond t f -> eliminate (eval scope ctx env cond) $ \case
      VNode TrueSig  -> eval scope ctx env t
      VNode FalseSig -> eval scope ctx env f
      Stuck cond'    -> vnode (IfSig cond' (eval scope ctx env t) (eval scope ctx env f))
    node -> evalNode scope ctx env node

-- | Normal form, inherited from the generic 'NbE.nf'.
nf :: Distinct n => Scope n -> BoolTm n -> BoolTm n
nf scope = NbE.nf scope NbE.NoContext
