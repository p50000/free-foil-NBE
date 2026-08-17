{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Showing lambda-pi values (the 'Value'-based semantic domain).
--
-- Terms have a 'Show' instance (in "LambdaPi.Generated"). Here we add two views
-- of a semantic value:
--
--   * 'ppValue' — the value's /meaning/: quote it back to a term and print it.
--   * 'ppValueStruct' (and the 'Show' instance) — the value's /structure/:
--     neutral variables, suspended nodes, and each closure's captured
--     environment, for inspecting the NbE representation itself.
module LambdaPi.PrettyPrint
  ( ppValue
  , ppValueStruct
  ) where

import FreeFoil.NbE
  ( ScopedClosure (ScopedClosure), ScopedAST (ScopedAST), Distinct, Scope
  , nameId, nameOf, quote, substitutionDomain
  )
import qualified FreeFoil.NbE as NbE
import LambdaPi (Value)
import LambdaPi.Generated (TermSig (AppSig, LamSig, PiSig), FFPattern (FFPatternVar), fromTerm)
import LambdaPi.Syntax.Print (printTree)

-- | Pretty-print a lambda-pi value by quoting it back to a term and printing.
-- Requires the scope the value lives in so that quoting can go under binders.
ppValue :: Distinct n => Scope n -> Value n -> String
ppValue scope = printTree . fromTerm . quote scope

-- | A structural rendering of a value: @#n@ for a neutral variable, and
-- @{node}@ for an evaluated node. Term subterms recurse; each scoped subterm
-- is shown as its raw suspended body together with its captured environment,
-- @body |env=[...]@.
ppValueStruct :: Value n -> String
ppValueStruct = \case
  NbE.VVar x -> '#' : show (nameId x)
  NbE.VNode node ->
    "{" ++ body ++ "}"
    where
      body = case node of
        AppSig f a ->
          "app " ++ ppValueStruct f ++ " " ++ ppValueStruct a
        LamSig sc ->
          "lam " ++ scoped sc
        PiSig d sc ->
          "pi " ++ ppValueStruct d ++ " " ++ scoped sc
  where
    scoped :: ScopedClosure FFPattern TermSig n -> String
    scoped (ScopedClosure env (ScopedAST b t)) =
      let dom = substitutionDomain env
          envS = if null dom then "" else " |env=" ++ show dom
      in binder b ++ ". " ++ show t ++ envS

    binder :: FFPattern i l -> String
    binder (FFPatternVar nb) = 'x' : show (nameId (nameOf nb))

instance Show (Value n) where
  show = ppValueStruct
