{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  , Declaration
  , checksUnder
  , typeIs
  ) where

import qualified Data.Map.Strict as Map
import qualified Control.Monad.Foil as Foil

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
  Node (PairSig a b) -> case NbE.force ty of
    NbE.VSuspended env (AnnSig _ (SigmaSig dom cod)) -> do
      a' <- check scope typing a dom
      b' <- check scope typing b (codomainAt scope typing env cod (evalIn scope typing a'))
      pure (annotated (quoteIn scope typing ty) (PairSig a' b'))
    _ -> Left ("a pair against a type that is not a Σ: " ++ show (quoteIn scope typing ty))
  Node (LamSig dom (ScopedAST pat body))
    | NbE.VSuspended env (AnnSig _ (PiSig piDom cod)) <- NbE.force ty -> case (assertDistinct pat, assertExt pat) of
        (Distinct, Ext) -> do
          (dom', _) <- inferType scope typing dom
          let domV = evalIn scope typing dom'
          if Conv.conv scope typing domV piDom
            then do
              (pat', typing') <- typedPattern scope typing pat domV
              let scope' = extendScopePattern pat scope
              body' <- check scope' typing' body (codomainAt scope' typing' (sink env) cod (patternValue scope' typing' pat'))
              pure (annotated (quoteIn scope typing ty) (LamSig dom' (ScopedAST pat' body')))
            else Left ("the domain " ++ show dom' ++ " is not " ++ show (quoteIn scope typing piDom))
  Node ReflSig -> case NbE.force ty of
    NbE.VNode (AnnSig _ (IdSig _ a b))
      | Conv.conv scope typing a b -> pure (annotated (quoteIn scope typing ty) ReflSig)
      | otherwise -> Left ("refl: " ++ show (quoteIn scope typing a) ++ " and " ++ show (quoteIn scope typing b) ++ " are not convertible")
    _ -> Left ("refl against a type that is not an identity type: " ++ show (quoteIn scope typing ty))
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
    case NbE.force funTy of
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
            pat' = TypedVar x dom'
        (body', bodyTy) <- infer scope' typing' body
        j <- levelOf typing' bodyTy
        let piTy = typeNode scope typing (max i j) (PiSig dom' (ScopedAST pat' (quoteIn scope' typing' bodyTy)))
        pure (annotated piTy (LamSig dom' (ScopedAST pat' body')), evalIn scope typing piTy)
    FFPatternPair {} -> Left "the type of a λ over a pair pattern is not inferred; check it against a Π type"
  Node (IdSig a x y) -> do
    (a', i) <- inferType scope typing a
    let aV = evalIn scope typing a'
    x' <- check scope typing x aV
    y' <- check scope typing y aV
    pure (annotated (universeTerm i) (IdSig a' x' y'), universe i)
  Node ReflSig -> Left "the type of refl is not inferred; check it against an identity type"
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
  case NbE.force ty of
    NbE.VSuspended env (AnnSig _ (SigmaSig a cod)) -> pure (p', a, codomainAt scope typing env cod)
    _ -> Left ("not a pair: " ++ show p')

-- | Infer the universe of a type.
inferType :: Distinct n => Scope n -> Typing n -> Raw n -> Either String (Elaborated n, Integer)
inferType scope typing ty = do
  (ty', u) <- infer scope typing ty
  case NbE.force u of
    NbE.VNode (AnnSig _ (UniverseSig i)) -> pure (ty', i)
    _ -> Left ("not a type: " ++ show ty')

-- | The level of the universe of a type value.
levelOf :: Typing n -> TypeValue n -> Either String Integer
levelOf typing ty = case NbE.force universeOf of
  NbE.VNode (AnnSig _ (UniverseSig i)) -> pure i
  _ -> Left "a type whose type is not a universe"
  where
    universeOf = case NbE.force ty of
      NbE.VVar x -> typeOf x typing
      NbE.VNode (AnnSig ann node) -> typeOfNode ann node
      NbE.VSuspended _ (AnnSig ann node) -> typeOfNode ann node

-- | A Π or Σ type: its domain is a type, and so is its codomain under the
-- bound name. It lives in the larger of their universes.
typeFormer ::
  Distinct n =>
  (Elaborated n -> ScopedAST TypedPattern Sig n -> TermSig (ScopedAST TypedPattern Sig n) (Elaborated n)) ->
  Scope n -> Typing n -> Raw n -> FFPattern n l -> Raw l -> Either String (Elaborated n, TypeValue n)
typeFormer former scope typing dom pat cod = case (assertDistinct pat, assertExt pat) of
  (Distinct, Ext) -> do
    (dom', i) <- inferType scope typing dom
    (pat', typing') <- typedPattern scope typing pat (evalIn scope typing dom')
    (cod', j) <- inferType (extendScopePattern pat scope) typing' cod
    pure (typeNode scope typing (max i j) (former dom' (ScopedAST pat' cod')), universe (max i j))

-- | A binder at a type, with the types of its names, and the context under
-- it: a variable at any type, a pair pattern at a Σ type, its first
-- component at the domain and its second at the codomain at the first.
typedPattern ::
  Distinct n =>
  Scope n -> Typing n -> FFPattern n l -> TypeValue n -> Either String (TypedPattern n l, Typing l)
typedPattern scope typing pat ty = case pat of
  FFPatternVar x -> case (assertDistinct x, assertExt x) of
    (Distinct, Ext) -> pure (TypedVar x (quoteIn scope typing ty), assume x ty typing)
  FFPatternPair l r -> case (NbE.force ty, assertDistinct l, assertExt l) of
    (NbE.VSuspended env (AnnSig _ (SigmaSig dom cod)), Distinct, Ext) -> do
      (l', typingL) <- typedPattern scope typing l dom
      let scopeL = extendScopePattern l scope
      (r', typingR) <- typedPattern scopeL typingL r (codomainAt scopeL typingL (sink env) cod (patternValue scopeL typingL l'))
      pure (TypedPair (quoteIn scope typing ty) l' r', typingR)
    _ -> Left ("a pair pattern at a type that is not a Σ: " ++ show (quoteIn scope typing ty))

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
typeNode :: Distinct n => Scope n -> Typing n -> Integer -> TermSig (ScopedAST TypedPattern Sig n) (Elaborated n) -> Elaborated n
typeNode scope typing level node = Node (AnnSig (typeAnnotation (universeTerm level) singleton) node)
  where
    singleton = isSingletonType (evalIn scope typing (annotated (universeTerm level) node))

-- | A node annotated with its type.
annotated :: Elaborated n -> TermSig (ScopedAST TypedPattern Sig n) (Elaborated n) -> Elaborated n
annotated ty = Node . AnnSig (HasType ty)

evalIn :: Distinct n => Scope n -> Typing n -> Elaborated n -> Value n
evalIn scope typing = NbE.eval scope typing identitySubst

quoteIn :: Distinct n => Scope n -> Typing n -> Value n -> Elaborated n
quoteIn = NbE.quote

-- | A declaration: a name, its type, and its body, or none for an
-- assumption. A body may use the names declared before it.
type Declaration = (String, String, Maybe String)

-- | Elaborate under declarations: declare each name in order, then run the
-- continuation in the scope, names and context of all of them.
underDeclarations ::
  forall a.
  [Declaration] ->
  (forall n. Distinct n => Scope n -> Map.Map String (Name n) -> Typing n -> Either String a) ->
  Either String a
underDeclarations declarations continue = go emptyScope Map.empty emptyTyping declarations
  where
    go :: Distinct n => Scope n -> Map.Map String (Name n) -> Typing n -> [Declaration] -> Either String a
    go scope names typing [] = continue scope names typing
    go scope names typing ((x, ty, body) : rest) = do
      ty0 <- parseOpen scope names ty
      (ty', _) <- inferType scope typing ty0
      let tyV = evalIn scope typing ty'
      body' <- traverse (\b -> parseOpen scope names b >>= \b0 -> check scope typing b0 tyV) body
      withFresh scope $ \b ->
        go (extendScope b scope)
           (Map.insert x (nameOf b) (Map.map Foil.sink names))
           (case body' of
              Just body'' -> define b tyV (evalIn scope typing body'') typing
              Nothing     -> assume b tyV typing)
           rest

-- | Whether a term checks against a type under declarations.
--
-- A λ over a pair pattern and a λ over a variable are convertible when
-- their bodies agree on one value, so @refl@ relates them:
--
-- >>> let sigma = "(a : A) * A"
-- >>> let swap = "\\((x, y) : " ++ sigma ++ "). (y, x)"
-- >>> let swap' = "\\(p : " ++ sigma ++ "). (second p, first p)"
-- >>> let t = "(p : " ++ sigma ++ ") -> (b : A) * A"
-- >>> checksUnder [("A", "U 0", Nothing), ("swap", t, Just swap), ("swap'", t, Just swap')] "refl" ("Id (" ++ t ++ ") swap swap'")
-- Right ()
checksUnder :: [Declaration] -> String -> String -> Either String ()
checksUnder declarations term ty = underDeclarations declarations $ \scope names typing -> do
  ty0 <- parseOpen scope names ty
  (ty', _) <- inferType scope typing ty0
  term0 <- parseOpen scope names term
  _ <- check scope typing term0 (evalIn scope typing ty')
  pure ()

-- | Whether the type of a term under definitions is the given type, read
-- off the value of the term and read back on the given side of the defined
-- names. A definition is a name, its type and its body; a body may use the
-- names defined before it.
--
-- The type is read off the folded head of the value, so a defined name
-- keeps the type its declaration gives it:
--
-- >>> import DependentTypes (Unfolding (..))
-- >>> let defs = [("T", "U 0", "(x : Unit) -> Unit"), ("f", "T", "\\(x : Unit). x")]
-- >>> typeIs Folded defs "f" "T"
-- Right True
-- >>> typeIs Folded defs "f" "(x : Unit) -> Unit"
-- Right False
--
-- Unfolded, the same type is the one the body computes:
--
-- >>> typeIs Unfolded defs "f" "(x : Unit) -> Unit"
-- Right True
typeIs :: Unfolding -> [(String, String, String)] -> String -> String -> Either String Bool
typeIs unfolding definitions term expected =
  underDeclarations [(x, ty, Just body) | (x, ty, body) <- definitions] $ \scope names typing -> do
    term0 <- parseOpen scope names term
    (term', _) <- infer scope typing term0
    let value = evalIn scope typing term'
        ty = quoteIn scope (withUnfolding unfolding typing) (typeOfValue typing value)
    expected0 <- parseOpen scope names expected
    (expected', _) <- inferType scope typing expected0
    pure (alphaEquiv scope (unannotated ty) (unannotated expected'))
