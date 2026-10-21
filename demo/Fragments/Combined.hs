{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TypeOperators    #-}
-- The specialisation rules and the printer are orphans on purpose: the Eval
-- instance of a sum lives in the library, and this is the module of the
-- language.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | A language composed from the fragments of functions, pairs and natural
-- numbers: its signature is the 'Sum' of theirs and its binders are 'Pat'.
-- The language writes no rule of its own. The 'Eval' instance is the one of
-- "FreeFoil.NbE.Sum", so 'nf', 'whnf' and conversion checking come from the
-- library; this module adds pattern synonyms over the sum, the specialisation
-- pragmas every language owes, and a printer.
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
  , Value
  , eval
  , nf
  , whnf
  ) where

import           Control.DeepSeq         (NFData (rnf))
import           Control.Monad.Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor.Sum      (Sum (..))
import           Data.ZipMatchK.Bifunctor ()

import           Fragments.Lambda        (LamF (..))
import           Fragments.Naturals      (NatF (..))
import           Fragments.Pairs         (PairF (..))
import           Fragments.Pattern       (Pat (..))
import           FreeFoil.NbE            (eval, nf, whnf)
import qualified FreeFoil.NbE            as NbE

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

-- | Terms print in the concrete syntax of the demo grammars, with variables
-- named by their foil identifiers.
instance Show (AST Pat Sig n) where
  showsPrec d = \case
    Var x -> shows x
    Lam binder body -> showParen (d > 0) $
      showString "\\" . showsPat binder . showString ". " . showsPrec 0 body
    App fun arg -> showParen (d > 10) $
      showsPrec 10 fun . showString " " . showsPrec 11 arg
    Pi dom binder cod -> showParen (d > 0) $
      showString "(" . showsPat binder . showString " : " . showsPrec 0 dom
        . showString ") -> " . showsPrec 0 cod
    Pair a b -> showString "(" . showsPrec 0 a . showString ", " . showsPrec 0 b . showString ")"
    Fst p -> showParen (d > 10) $ showString "fst " . showsPrec 11 p
    Snd p -> showParen (d > 10) $ showString "snd " . showsPrec 11 p
    Split p binder body -> showParen (d > 0) $
      showString "split " . showsPrec 0 p . showString " as " . showsPat binder
        . showString " in " . showsPrec 0 body
    Zero -> showString "zero"
    Suc t -> showParen (d > 10) $ showString "suc " . showsPrec 11 t
    NatRec n z binder s -> showParen (d > 10) $
      showString "natrec " . showsPrec 11 n . showString " { zero -> " . showsPrec 0 z
        . showString " ; suc " . showsPat binder . showString " -> " . showsPrec 0 s
        . showString " }"
    where
      showsPat :: Pat n l -> ShowS
      showsPat = \case
        PatVar x -> shows (nameOf x)
        PatPair x y -> showString "(" . shows (nameOf x) . showString ", " . shows (nameOf y) . showString ")"
