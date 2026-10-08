{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
-- | Booleans with @if@: a second object language, without binders, showing
-- that the core is generic in the signature. The language is this signature
-- plus one 'Eval' instance; evaluation and normalisation are inherited.
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
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor)

import FreeFoil.NbE (Eval (evalSig), Value (VNode), eval, evalNode, nfNbe)

-- | Two introduction forms and one eliminator; no scoped positions.
data BoolSig scope term
  = TrueSig
  | FalseSig
  | IfSig term term term
  deriving (Functor)

deriveBifunctor ''BoolSig
deriveBifoldable ''BoolSig

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

-- | The one elimination rule: a canonical condition selects a branch, a
-- neutral condition leaves the @if@ stuck.
instance Eval NameBinder BoolSig where
  evalSig scope env = \case
    IfSig cond t f -> case eval scope env cond of
      VNode TrueSig  -> eval scope env t
      VNode FalseSig -> eval scope env f
      cond'          -> VNode (IfSig cond' (eval scope env t) (eval scope env f))
    node -> evalNode (eval scope) env node

-- | Normal form, inherited from the generic 'nfNbe'.
nf :: Distinct n => Scope n -> BoolTm n -> BoolTm n
nf = nfNbe
