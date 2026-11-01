{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | Bidirectional elaboration of the dependent types language: a term is checked
-- against a type or its type is inferred, and the result carries the types
-- that normalisation needs (see "DependentTypes"). Types are values, and
-- elaboration compares them with the language's own conversion, in the
-- context of the types of the names in scope.
--
-- The universe has itself as its type. A pair is checked against a Σ type
-- and a λ against a Π type. Every other term is inferred, then compared with
-- the type it is checked against.
--
-- The algorithm is the standard bidirectional one (see the survey of
-- Dunfield and Krishnaswami, "Bidirectional Typing", 2021), with types as
-- values computed by normalisation by evaluation.
module DependentTypes.Elaborate
  ( check
  , infer
  , elaborate
  ) where

import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Control.Monad.Free.Foil.Annotated (AnnSig (..))
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import DependentTypes
import DependentTypes.Generated (FFPattern (..), TermSig (..))
import DependentTypes.Parser (parseOpen)

-- | Check a term against a type.
check :: Distinct n => Scope n -> Typing n -> Raw n -> Value n -> Either String (Elaborated n)
check scope typing term ty = case term of
  Node (PairSig a b) -> case ty of
    NbE.VSuspended _ (AnnSig _ (SigmaSig dom _)) -> do
      a' <- check scope typing a dom
      b' <- check scope typing b (codomainAt scope typing ty (evalIn scope typing a'))
      pure (node (PairSig a' b'))
    _ -> Left ("a pair against a type that is not a Σ: " ++ show (quoteIn scope typing ty))
  Node (LamSig dom (ScopedAST pat body))
    | NbE.VSuspended _ (AnnSig _ (PiSig piDom _)) <- ty -> case pat of
        FFPatternVar x -> case (assertDistinct x, assertExt x) of
          (Distinct, Ext) -> do
            dom' <- check scope typing dom universe
            let domV = evalIn scope typing dom'
            if Conv.conv scope typing domV piDom
              then do
                let scope' = extendScope x scope
                    typing' = assume x domV typing
                body' <- check scope' typing' body (codomainAt scope' typing' (sink ty) (NbE.VVar (nameOf x)))
                pure (node (LamSig dom' (ScopedAST pat body')))
              else Left ("the domain " ++ show dom' ++ " is not " ++ show (quoteIn scope typing piDom))
  _ -> do
    (term', ty') <- infer scope typing term
    if Conv.conv scope typing ty' ty
      then pure term'
      else Left ("type mismatch: " ++ show term' ++ " has type " ++ show (quoteIn scope typing ty')
                 ++ ", not " ++ show (quoteIn scope typing ty))

-- | Infer the type of a term.
infer :: Distinct n => Scope n -> Typing n -> Raw n -> Either String (Elaborated n, Value n)
infer scope typing = \case
  Var x -> pure (Var x, typeOf x typing)
  Node UniverseSig -> pure (node UniverseSig, universe)
  Node UnitSig -> pure (node UnitSig, universe)
  Node TTSig -> pure (node TTSig, unitType)
  Node (AppSig fun arg) -> do
    (fun', funTy) <- infer scope typing fun
    case funTy of
      NbE.VSuspended _ (AnnSig _ (PiSig dom _)) -> do
        arg' <- check scope typing arg dom
        let ty = codomainAt scope typing funTy (evalIn scope typing arg')
        pure (annotated (quoteIn scope typing ty) (AppSig fun' arg'), ty)
      _ -> Left ("not a function: " ++ show fun')
  Node (LamSig dom (ScopedAST pat body)) -> case pat of
    FFPatternVar x -> case (assertDistinct x, assertExt x) of
      (Distinct, Ext) -> do
        dom' <- check scope typing dom universe
        let scope' = extendScope x scope
            typing' = assume x (evalIn scope typing dom') typing
        (body', bodyTy) <- infer scope' typing' body
        let piTy = node (PiSig dom' (ScopedAST pat (quoteIn scope' typing' bodyTy)))
        pure (node (LamSig dom' (ScopedAST pat body')), evalIn scope typing piTy)
  Node (PiSig dom (ScopedAST pat cod)) -> typeFormer PiSig scope typing dom pat cod
  Node (SigmaSig dom (ScopedAST pat cod)) -> typeFormer SigmaSig scope typing dom pat cod
  Node (FirstSig p) -> do
    (p', _, a) <- inferPair scope typing p
    pure (annotated (quoteIn scope typing a) (FirstSig p'), a)
  Node (SecondSig p) -> do
    (p', ty, a) <- inferPair scope typing p
    let first = evalIn scope typing (annotated (quoteIn scope typing a) (FirstSig p'))
        b = codomainAt scope typing ty first
    pure (annotated (quoteIn scope typing b) (SecondSig p'), b)
  Node (PairSig _ _) -> Left "the type of a pair is not inferred; check it against a Σ type"

-- | Infer the type of a term that is projected: a Σ type, and its domain.
inferPair :: Distinct n => Scope n -> Typing n -> Raw n -> Either String (Elaborated n, Value n, Value n)
inferPair scope typing p = do
  (p', ty) <- infer scope typing p
  case ty of
    NbE.VSuspended _ (AnnSig _ (SigmaSig a _)) -> pure (p', ty, a)
    _ -> Left ("not a pair: " ++ show p')

-- | A Π or Σ type: its domain is a type, and so is its codomain under the
-- bound name.
typeFormer ::
  Distinct n =>
  (Elaborated n -> ScopedAST FFPattern Sig n -> TermSig (ScopedAST FFPattern Sig n) (Elaborated n)) ->
  Scope n -> Typing n -> Raw n -> FFPattern n l -> Raw l -> Either String (Elaborated n, Value n)
typeFormer former scope typing dom pat cod = case pat of
  FFPatternVar x -> case (assertDistinct x, assertExt x) of
    (Distinct, Ext) -> do
      dom' <- check scope typing dom universe
      cod' <- check (extendScope x scope) (assume x (evalIn scope typing dom') typing) cod universe
      pure (node (former dom' (ScopedAST pat cod')), universe)

-- | Elaborate a closed term against a closed type, both parsed from strings.
-- The result is the elaborated term and its type.
elaborate :: String -> String -> Either String (Elaborated VoidS, Elaborated VoidS)
elaborate term ty = do
  ty0 <- parseOpen emptyScope Map.empty ty
  term0 <- parseOpen emptyScope Map.empty term
  ty' <- check emptyScope emptyTyping ty0 universe
  term' <- check emptyScope emptyTyping term0 (evalIn emptyScope emptyTyping ty')
  pure (term', ty')

-- | A node annotated 'Nothing'.
node :: TermSig (ScopedAST FFPattern Sig n) (Elaborated n) -> Elaborated n
node = Node . AnnSig Nothing

-- | An eliminator annotated with the type of its result.
annotated :: Elaborated n -> TermSig (ScopedAST FFPattern Sig n) (Elaborated n) -> Elaborated n
annotated ty = Node . AnnSig (Just ty)

evalIn :: Distinct n => Scope n -> Typing n -> Elaborated n -> Value n
evalIn scope typing = NbE.eval scope typing identitySubst

quoteIn :: Distinct n => Scope n -> Typing n -> Value n -> Elaborated n
quoteIn = NbE.quote
