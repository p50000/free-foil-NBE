{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures -Wno-redundant-constraints -Wno-orphans #-}

-- | Scope-safe lambda-pi syntax, together with the raw/scoped conversions,
-- all generated from "LambdaPi.Raw" by free-foil's Template Haskell.
--
-- This module is the whole of the "describe the language and get scope-safe
-- syntax" story: the signature bifunctor @TermSig@, the term type
-- @FFTerm = 'AST' FFPattern TermSig@, the pattern synonyms (@FFApp@, @FFLam@,
-- @FFPi@), and the conversions @toTerm@ / @fromTerm@ are all produced by
-- 'mkFreeFoil' and 'mkFreeFoilConversions'.
module LambdaPi.Generated where

import Control.DeepSeq (NFData (rnf))
import qualified Control.Monad.Foil as Foil
import Control.Monad.Free.Foil (AST)
import Control.Monad.Free.Foil.TH.MkFreeFoil
import Data.Bifunctor.TH
import Data.ZipMatchK
import Generics.Kind.TH (deriveGenericK)

import LambdaPi.Raw
import LambdaPi.Syntax.Print (printTree)

mkFreeFoil config

deriveGenericK ''FFPattern
instance Foil.SinkableK FFPattern
instance Foil.HasNameBinders FFPattern
instance Foil.CoSinkable FFPattern
instance Foil.UnifiablePattern FFPattern

deriveBifunctor ''TermSig
deriveBifoldable ''TermSig
deriveBitraversable ''TermSig

deriveGenericK ''TermSig
instance ZipMatchK VarIdent where zipMatchWithK = zipMatchViaEq
instance ZipMatchK TermSig

mkFreeFoilConversions config

-- | Show scope-safe terms via the generated raw conversion and BNFC's printer.
-- Defined here (where @TermSig@ and @FFPattern@ live) so the instance is not an
-- orphan. Names variables by foil identifier, so the output is not
-- alpha-canonical but round-trips through the parser.
instance Show (AST FFPattern TermSig n) where
  show = printTree . fromTerm

-- | Feed free-foil's generic @NFData (AST binder sig)@: it needs @NFData@ for
-- the binder and the signature node. Enables deep-forcing terms for benchmarks
-- and harnesses that require @NFData@.
instance NFData (FFPattern x y) where
  rnf (FFPatternVar nb) = rnf (Foil.nameId (Foil.nameOf nb))

instance (NFData scope, NFData term) => NFData (TermSig scope term)
