{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the Eval instance belongs with the rules
-- | The monolithic demonstration language: functions, pairs and natural
-- numbers in one signature, written the way a language is written without
-- fragments, for comparison with "Fragments.Combined", which composes the
-- same language from "Fragments.Lambda", "Fragments.Pairs" and
-- "Fragments.Naturals". The three rules are those of "LambdaPi",
-- "Pairs" and "Naturals". The syntax is generated in
-- "Monolith.Generated"; this module adds the 'Eval' instance.
--
-- A pattern binds one name or two, for every binder, so a lambda over a pair
-- of names or a @split@ over one name is syntactically possible; the rules
-- reject them.
module Monolith
  ( Monolith
  , Pattern (..)
  , TermSig (..)
  , pattern Var
  , pattern Lam
  , pattern App
  , pattern Pi
  , pattern Pair
  , pattern Fst
  , pattern Snd
  , pattern Split
  , pattern Zero
  , pattern Suc
  , pattern NatRec
  , numeral
  , Value
  , eval
  , nf
  , whnf
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Context, Eval (..), eval, nf, whnf)
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import Monolith.Generated

-- | Terms of the monolithic language in scope @n@.
type Monolith n = Term n

-- | Semantic values of the monolithic language.
type Value = NbE.Value Pattern TermSig

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Monolith n -> Monolith n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> Substitution Value i o -> Monolith i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Value n -> Monolith n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> Value n -> Value n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> Monolith n -> Monolith n -> Bool #-}

-- | The numeral of a natural number.
numeral :: Int -> Monolith n
numeral k = iterate Suc Zero !! k

-- | The three elimination rules, side by side, each as in its standalone
-- language: β, the projections and @split@, and primitive recursion. A
-- binder of the wrong shape is an error.
instance Context ctx => Eval ctx Pattern TermSig where
  evalSig ctx env = \case
    AppSig fun arg ->
      case eval ctx env fun of
        NbE.VSuspended env' (LamSig (ScopedAST (PatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> eval ctx (addSubst env' binder (eval ctx env arg)) body
        NbE.VSuspended _ (LamSig (ScopedAST PatternPair {} _)) ->
          error "Monolith: a lambda binds one name"
        fun' -> NbE.VNode (AppSig fun' (eval ctx env arg))
    FstSig p ->
      case eval ctx env p of
        NbE.VNode (PairSig a _) -> a
        p'                     -> NbE.VNode (FstSig p')
    SndSig p ->
      case eval ctx env p of
        NbE.VNode (PairSig _ b) -> b
        p'                     -> NbE.VNode (SndSig p')
    SplitSig p (ScopedAST (PatternPair x y) body) ->
      case eval ctx env p of
        NbE.VNode (PairSig a b) ->
          case assertDistinct (PatternPair x y) of
            Distinct -> eval ctx (addSubst (addSubst env x a) y b) body
        p' -> NbE.VSuspended env (SplitSig p' (ScopedAST (PatternPair x y) body))
    SplitSig _ (ScopedAST PatternVar {} _) ->
      error "Monolith: split binds two names"
    NatRecSig n z (ScopedAST (PatternPair k r) s) ->
      case assertDistinct (PatternPair k r) of
        Distinct ->
          let zeroCase = eval ctx env z
              recurse m = case m of
                NbE.VNode ZeroSig    -> zeroCase
                NbE.VNode (SucSig p) -> eval ctx (addSubst (addSubst env k p) r (recurse p)) s
                m' -> NbE.VSuspended env (NatRecSig m' zeroCase (ScopedAST (PatternPair k r) s))
          in recurse (eval ctx env n)
    NatRecSig _ _ (ScopedAST PatternVar {} _) ->
      error "Monolith: the suc branch of natrec binds two names"
    node -> NbE.evalNode ctx env node
