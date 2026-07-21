{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Showing lambda-pi values (the 'Closure'-based semantic domain).
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
  ( Closure (Closure, VarC), ScopedAST (ScopedAST), Distinct, Scope
  , nameId, nameOf, quote', substitutionDomain
  )
import LambdaPi (Value, eval)
import LambdaPi.Generated (TermSig (AppSig, LamSig, PiSig), FFPattern (FFPatternVar), fromTerm)
import LambdaPi.Syntax.Print (printTree)

-- | Pretty-print a lambda-pi value by quoting it back to a term and printing.
-- Requires the scope the value lives in so that quoting can go under binders.
ppValue :: Distinct n => Scope n -> Value n -> String
ppValue scope = printTree . fromTerm . quote' eval scope

-- | A structural rendering of a value: @#n@ for a neutral variable, and
-- @{node |env=[...]}@ for a suspended closure (term subterms recurse; scoped
-- subterms are shown as their raw suspended AST).
ppValueStruct :: Value n -> String
ppValueStruct = \case
  VarC x -> '#' : show (nameId x)
  Closure env node ->
    let dom = substitutionDomain env
        envS = if null dom then "" else " |env=" ++ show dom
        body = case node of
          AppSig f a ->
            "app " ++ ppValueStruct f ++ " " ++ ppValueStruct a
          LamSig (ScopedAST b t) ->
            "lam " ++ binder b ++ ". " ++ show t
          PiSig d (ScopedAST b t) ->
            "pi " ++ ppValueStruct d ++ " " ++ binder b ++ ". " ++ show t
    in "{" ++ body ++ envS ++ "}"
  where
    binder :: FFPattern i l -> String
    binder (FFPatternVar nb) = 'x' : show (nameId (nameOf nb))

instance Show (Value n) where
  show = ppValueStruct
