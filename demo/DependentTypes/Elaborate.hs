{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | Bidirectional elaboration of the dependent types language. A term is
-- checked against a type, or its type is inferred, and the result carries
-- the types that normalisation needs (see "DependentTypes"). Types are
-- values, compared with the language's own conversion.
--
-- A pair is checked against a Σ type and a λ against a Π type. Every other
-- term is inferred, and its type must be a subtype of the type it is checked
-- against (see "DependentTypes"). A universe @U i@ has type @U (i + 1)@, and a
-- Π or Σ type lives in the larger universe of its domain and codomain. The
-- domain of a λ is compared with that of its Π type by conversion.
--
-- The algorithm is Coquand's ("An algorithm for type-checking dependent
-- types", 1996): checking and inference with types as values, a λ checked
-- against a Π, and an inferred type compared with the expected one by
-- conversion. Dunfield and Krishnaswami survey bidirectional typing
-- ("Bidirectional Typing", 2021, §9.1 on this algorithm). The rules for Σ,
-- pairs, projections and the unit type, and the annotations, are additions
-- to it.
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
check :: Distinct n => Scope n -> Typing n -> Raw n -> TypeValue n -> Either String (Elaborated n)
check scope typing term ty = case term of
  Node (PairSig a b) -> case ty of
    NbE.VSuspended env (AnnSig _ (SigmaSig dom cod)) -> do
      a' <- check scope typing a dom
      b' <- check scope typing b (codomainAt scope typing env cod (evalIn scope typing a'))
      pure (annotated (quoteIn scope typing ty) (PairSig a' b'))
    _ -> Left ("a pair against a type that is not a Σ: " ++ show (quoteIn scope typing ty))
  Node (LamSig dom (ScopedAST pat body))
    | NbE.VSuspended env (AnnSig _ (PiSig piDom cod)) <- ty -> case pat of
        FFPatternVar x -> case (assertDistinct x, assertExt x) of
          (Distinct, Ext) -> do
            (dom', _) <- inferType scope typing dom
            let domV = evalIn scope typing dom'
            if Conv.conv scope typing domV piDom
              then do
                let scope' = extendScope x scope
                    typing' = assume x domV typing
                body' <- check scope' typing' body (codomainAt scope' typing' (sink env) cod (NbE.VVar (nameOf x)))
                pure (annotated (quoteIn scope typing ty) (LamSig dom' (ScopedAST pat body')))
              else Left ("the domain " ++ show dom' ++ " is not " ++ show (quoteIn scope typing piDom))
  _ -> do
    (term', ty') <- infer scope typing term
    if isSubtype scope typing ty' ty
      then pure term'
      else Left ("type mismatch: " ++ show term' ++ " has type " ++ show (quoteIn scope typing ty')
                 ++ ", not " ++ show (quoteIn scope typing ty))

-- | Infer the type of a term.
infer :: Distinct n => Scope n -> Typing n -> Raw n -> Either String (Elaborated n, TypeValue n)
infer scope typing = \case
  Var x -> pure (Var x, typeOf x typing)
  Node (UniverseSig i) -> pure (universeTerm i, universe (i + 1))
  Node UnitSig -> pure (unitTerm, universe 0)
  Node TTSig -> pure (annotated unitTerm TTSig, unitType)
  Node (AppSig fun arg) -> do
    (fun', funTy) <- infer scope typing fun
    case funTy of
      NbE.VSuspended env (AnnSig _ (PiSig dom cod)) -> do
        arg' <- check scope typing arg dom
        let ty = codomainAt scope typing env cod (evalIn scope typing arg')
        pure (annotated (quoteIn scope typing ty) (AppSig fun' arg'), ty)
      _ -> Left ("not a function: " ++ show fun')
  Node (LamSig dom (ScopedAST pat body)) -> case pat of
    FFPatternVar x -> case (assertDistinct x, assertExt x) of
      (Distinct, Ext) -> do
        (dom', i) <- inferType scope typing dom
        let scope' = extendScope x scope
            typing' = assume x (evalIn scope typing dom') typing
        (body', bodyTy) <- infer scope' typing' body
        j <- levelOf typing' bodyTy
        let piTy = typeNode scope typing (max i j) (PiSig dom' (ScopedAST pat (quoteIn scope' typing' bodyTy)))
        pure (annotated piTy (LamSig dom' (ScopedAST pat body')), evalIn scope typing piTy)
  Node (PiSig dom (ScopedAST pat cod)) -> typeFormer PiSig scope typing dom pat cod
  Node (SigmaSig dom (ScopedAST pat cod)) -> typeFormer SigmaSig scope typing dom pat cod
  Node (FirstSig p) -> do
    (p', a, _) <- inferPair scope typing p
    pure (annotated (quoteIn scope typing a) (FirstSig p'), a)
  Node (SecondSig p) -> do
    (p', a, codomain) <- inferPair scope typing p
    let first = evalIn scope typing (annotated (quoteIn scope typing a) (FirstSig p'))
        b = codomain first
    pure (annotated (quoteIn scope typing b) (SecondSig p'), b)
  Node (PairSig _ _) -> Left "the type of a pair is not inferred; check it against a Σ type"

-- | Infer the type of a term that is projected, a Σ type: its domain, and
-- its codomain at a value.
inferPair ::
  Distinct n =>
  Scope n -> Typing n -> Raw n -> Either String (Elaborated n, TypeValue n, Value n -> TypeValue n)
inferPair scope typing p = do
  (p', ty) <- infer scope typing p
  case ty of
    NbE.VSuspended env (AnnSig _ (SigmaSig a cod)) -> pure (p', a, codomainAt scope typing env cod)
    _ -> Left ("not a pair: " ++ show p')

-- | Infer the universe of a type.
inferType :: Distinct n => Scope n -> Typing n -> Raw n -> Either String (Elaborated n, Integer)
inferType scope typing ty = do
  (ty', u) <- infer scope typing ty
  case u of
    NbE.VNode (AnnSig _ (UniverseSig i)) -> pure (ty', i)
    _ -> Left ("not a type: " ++ show ty')

-- | The level of the universe of a type value.
levelOf :: Typing n -> TypeValue n -> Either String Integer
levelOf typing ty = case universeOf of
  NbE.VNode (AnnSig _ (UniverseSig i)) -> pure i
  _ -> Left "a type whose type is not a universe"
  where
    universeOf = case ty of
      NbE.VVar x -> typeOf x typing
      NbE.VNode (AnnSig ann node) -> typeOfNode ann node
      NbE.VSuspended _ (AnnSig ann node) -> typeOfNode ann node

-- | A Π or Σ type: its domain is a type, and so is its codomain under the
-- bound name. It lives in the larger of their universes.
typeFormer ::
  Distinct n =>
  (Elaborated n -> ScopedAST FFPattern Sig n -> TermSig (ScopedAST FFPattern Sig n) (Elaborated n)) ->
  Scope n -> Typing n -> Raw n -> FFPattern n l -> Raw l -> Either String (Elaborated n, TypeValue n)
typeFormer former scope typing dom pat cod = case pat of
  FFPatternVar x -> case (assertDistinct x, assertExt x) of
    (Distinct, Ext) -> do
      (dom', i) <- inferType scope typing dom
      (cod', j) <- inferType (extendScope x scope) (assume x (evalIn scope typing dom') typing) cod
      pure (typeNode scope typing (max i j) (former dom' (ScopedAST pat cod')), universe (max i j))

-- | Elaborate a closed term against a closed type, both parsed from strings.
-- The result is the elaborated term and its type.
elaborate :: String -> String -> Either String (Elaborated VoidS, Elaborated VoidS)
elaborate term ty = do
  ty0 <- parseOpen emptyScope Map.empty ty
  term0 <- parseOpen emptyScope Map.empty term
  (ty', _) <- inferType emptyScope emptyTyping ty0
  term' <- check emptyScope emptyTyping term0 (evalIn emptyScope emptyTyping ty')
  pure (term', ty')

-- | The universe of a level, which has no annotation.
universeTerm :: Integer -> Elaborated n
universeTerm i = Node (AnnSig IsUniverse (UniverseSig i))

-- | The unit type, a singleton in the lowest universe.
unitTerm :: Elaborated n
unitTerm = Node (AnnSig (IsSingletonType (universeTerm 0)) UnitSig)

-- | A Π or Σ type in the universe of a level, annotated with whether it is a
-- singleton, as its value decides.
typeNode :: Distinct n => Scope n -> Typing n -> Integer -> TermSig (ScopedAST FFPattern Sig n) (Elaborated n) -> Elaborated n
typeNode scope typing level node = Node (AnnSig (typeAnnotation (universeTerm level) singleton) node)
  where
    singleton = isSingletonType (evalIn scope typing (annotated (universeTerm level) node))

-- | A node annotated with its type.
annotated :: Elaborated n -> TermSig (ScopedAST FFPattern Sig n) (Elaborated n) -> Elaborated n
annotated ty = Node . AnnSig (HasType ty)

evalIn :: Distinct n => Scope n -> Typing n -> Elaborated n -> Value n
evalIn scope typing = NbE.eval scope typing identitySubst

quoteIn :: Distinct n => Scope n -> Typing n -> Value n -> Elaborated n
quoteIn = NbE.quote
