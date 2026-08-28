{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- | A second object language — Booleans with @if@ — used to demonstrate that
-- the 'FreeFoil.NbE.Eval' class and the generic 'FreeFoil.NbE.nfNbe' are
-- genuinely signature-generic, not lambda-pi-shaped. The whole language is this
-- signature plus one 'FreeFoil.NbE.Eval' instance (see below); evaluation and
-- normalisation are inherited unchanged from "FreeFoil.NbE".
module Booleans
  ( BoolSig (..)
  , BoolTm
  , pattern TT
  , pattern FF
  , pattern If
  , nf
  ) where

import Control.Monad.Free.Foil (AST (Node))
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor)

import FreeFoil.NbE (Eval (evalSig), Value (VNode), NameBinder, Scope, Distinct, eval, evalNode, nfNbe)

-- | Signature for a Booleans language: two introduction forms ('TrueSig',
-- 'FalseSig') and one eliminator ('IfSig'). There are no scoped positions —
-- Booleans bind nothing — so the @scope@ parameter is unused.
data BoolSig scope term
  = TrueSig
  | FalseSig
  | IfSig term term term
  deriving (Functor, Foldable)

deriveBifunctor ''BoolSig
deriveBifoldable ''BoolSig

-- | Boolean terms. The binder type is the standard 'NameBinder', but it is
-- never used (the signature has no scoped positions).
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

-- | The whole object-language contribution: the one elimination rule, @if@. A
-- 'True'\/'False' condition selects a branch; a neutral (e.g. variable-headed)
-- condition leaves the @if@ stuck. 'TrueSig'\/'FalseSig' are introduction forms
-- and fall through to the generic default. Everything else — variable lookup,
-- recursion, quoting, 'nf' — is inherited unchanged from "FreeFoil.NbE".
--
-- ('evalSig' receives the raw node and the current environment; the eliminator
-- evaluates its own subterms. Booleans have no scoped positions, so no
-- 'FreeFoil.NbE.ScopedClosure' arises.)
instance Eval NameBinder BoolSig where
  evalSig scope env = \case
    IfSig cond t f -> case eval scope env cond of
      VNode TrueSig  -> eval scope env t
      VNode FalseSig -> eval scope env f
      cond'          -> VNode (IfSig cond' (eval scope env t) (eval scope env f))
    node -> evalNode (eval scope) env node

-- | Normal form by NbE, inherited unchanged from the generic 'nfNbe'.
nf :: Distinct n => Scope n -> BoolTm n -> BoolTm n
nf = nfNbe
