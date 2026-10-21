{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TypeOperators    #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the language is a synonym over library types
-- | A language composed from the fragments of functions, pairs and natural
-- numbers: its signature is the 'Sum' of theirs and its binders are 'Pat'.
-- The language writes no rule of its own. The 'Eval' instance is the one of
-- "FreeFoil.NbE.Sum", so 'nf', 'whnf' and conversion checking come from the
-- library; this module adds pattern synonyms over the sum, the specialisation
-- pragmas every language owes, and the conversions to and from "Monolith",
-- the same language in one signature, which lends it a parser and a printer.
module Fragments.Combined
  ( Sig
  , Combined
  , Pat (..)
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
  , toMonolith
  , fromMonolith
  , Value
  , eval
  , nf
  , whnf
  ) where

import           Control.DeepSeq         (NFData (rnf))
import           Control.Monad.Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor.Sum      (Sum (..))
import           Data.String             (IsString (..))
import           Data.ZipMatchK.Bifunctor ()

import           Fragments.Lambda        (LamF (..))
import           Fragments.Naturals      (NatF (..))
import           Fragments.Pairs         (PairF (..))
import           Fragments.Pattern       (Pat (..))
import           FreeFoil.NbE            (eval, nf, whnf)
import qualified FreeFoil.NbE            as NbE
import qualified Monolith
import           Monolith.Parser         (parseMonolith)

-- | The signature: functions, then pairs, then naturals.
type Sig = Sum LamF (Sum PairF NatF)

-- | Terms of the composed language in scope @n@.
type Combined n = AST Pat Sig n

-- | Semantic values of the composed language.
type Value = NbE.Value Pat Sig

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Combined n -> Combined n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> Substitution Value i o -> Combined i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Value n -> Combined n #-}

pattern Lam :: Pat n l -> Combined l -> Combined n
pattern Lam binder body = Node (L2 (LamF (ScopedAST binder body)))

pattern App :: Combined n -> Combined n -> Combined n
pattern App fun arg = Node (L2 (AppF fun arg))

pattern Pi :: Combined n -> Pat n l -> Combined l -> Combined n
pattern Pi dom binder cod = Node (L2 (PiF dom (ScopedAST binder cod)))

pattern Pair :: Combined n -> Combined n -> Combined n
pattern Pair a b = Node (R2 (L2 (PairF a b)))

pattern Fst :: Combined n -> Combined n
pattern Fst p = Node (R2 (L2 (FstF p)))

pattern Snd :: Combined n -> Combined n
pattern Snd p = Node (R2 (L2 (SndF p)))

pattern Split :: Combined n -> Pat n l -> Combined l -> Combined n
pattern Split p binder body = Node (R2 (L2 (SplitF p (ScopedAST binder body))))

pattern Zero :: Combined n
pattern Zero = Node (R2 (R2 ZeroF))

pattern Suc :: Combined n -> Combined n
pattern Suc t = Node (R2 (R2 (SucF t)))

pattern NatRec :: Combined n -> Combined n -> Pat n l -> Combined l -> Combined n
pattern NatRec n z binder s = Node (R2 (R2 (NatRecF n z (ScopedAST binder s))))

{-# COMPLETE Var, Lam, App, Pi, Pair, Fst, Snd, Split, Zero, Suc, NatRec #-}

-- | Forcing a sum forces the summand; bifunctors has no such instance.
instance (NFData (f scope term), NFData (g scope term)) => NFData (Sum f g scope term) where
  rnf (L2 x) = rnf x
  rnf (R2 y) = rnf y

-- | The numeral of a natural number.
numeral :: Int -> Combined n
numeral k = iterate Suc Zero !! k

-- * The monolithic language as concrete syntax

-- | The same term in the monolithic language, which lends the composed one
-- its parser and printer.
toMonolith :: Combined n -> Monolith.Monolith n
toMonolith = \case
  Var x -> Monolith.Var x
  Lam pat body -> Monolith.Lam (toPat pat) (toMonolith body)
  App fun arg -> Monolith.App (toMonolith fun) (toMonolith arg)
  Pi dom pat cod -> Monolith.Pi (toMonolith dom) (toPat pat) (toMonolith cod)
  Pair a b -> Monolith.Pair (toMonolith a) (toMonolith b)
  Fst p -> Monolith.Fst (toMonolith p)
  Snd p -> Monolith.Snd (toMonolith p)
  Split p pat body -> Monolith.Split (toMonolith p) (toPat pat) (toMonolith body)
  Zero -> Monolith.Zero
  Suc t -> Monolith.Suc (toMonolith t)
  NatRec n z pat s -> Monolith.NatRec (toMonolith n) (toMonolith z) (toPat pat) (toMonolith s)
  where
    toPat :: Pat n l -> Monolith.FFPattern n l
    toPat (PatVar x)    = Monolith.FFPatternVar x
    toPat (PatPair x y) = Monolith.FFPatternPair x y

-- | The same term in the composed language.
fromMonolith :: Monolith.Monolith n -> Combined n
fromMonolith = \case
  Monolith.Var x -> Var x
  Monolith.Lam pat body -> Lam (fromPat pat) (fromMonolith body)
  Monolith.App fun arg -> App (fromMonolith fun) (fromMonolith arg)
  Monolith.Pi dom pat cod -> Pi (fromMonolith dom) (fromPat pat) (fromMonolith cod)
  Monolith.Pair a b -> Pair (fromMonolith a) (fromMonolith b)
  Monolith.Fst p -> Fst (fromMonolith p)
  Monolith.Snd p -> Snd (fromMonolith p)
  Monolith.Split p pat body -> Split (fromMonolith p) (fromPat pat) (fromMonolith body)
  Monolith.Zero -> Zero
  Monolith.Suc t -> Suc (fromMonolith t)
  Monolith.NatRec n z pat s -> NatRec (fromMonolith n) (fromMonolith z) (fromPat pat) (fromMonolith s)
  where
    fromPat :: Monolith.FFPattern n l -> Pat n l
    fromPat (Monolith.FFPatternVar x)    = PatVar x
    fromPat (Monolith.FFPatternPair x y) = PatPair x y

-- | Terms print through the monolithic language and BNFC's printer.
instance Show (AST Pat Sig n) where
  show = show . toMonolith

-- | A closed term parsed by the monolithic language's parser.
instance IsString (Combined VoidS) where
  fromString = either (error . ("Fragments.Combined: " ++)) fromMonolith . parseMonolith
