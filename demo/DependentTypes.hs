{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
-- The Show instance of a synonym over library types.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dependent functions and pairs over a universe, with a unit type: a
-- language whose context holds types. Its terms are elaborated (see
-- "DependentTypes.Elaborate"): every binder carries its type, and an
-- eliminator, an application or a @split@, carries the type of its result
-- as free-foil's annotation. Every other node is annotated 'Nothing'.
--
-- Under a binder the language gives its names their types
-- ('NbE.extendScopedWith'): the domain under @λ@, @Π@ and @Σ@, and under
-- @split p : (a : A) * B as (x, y) in t@ the type @A@ for @x@ and @B@ at @x@
-- for @y@, evaluated in the context that already has @x@.
--
-- The types decide η ('NbE.refineVar', 'NbE.refineSig'). A neutral of type
-- @Unit@ is @tt@, and a neutral @f@ of type @(x : A) -> B@ is
-- @\\(x : A). f x@. A variable finds its type in the context, an eliminator
-- in its annotation. So in a context of
-- types ('Typing') @\\(x : Unit). x@ normalises to @\\(x : Unit). tt@, while
-- with 'NbE.NoContext' variables have no types. Pairs have no η, since the
-- language has no projections.
--
-- The grammar follows the monolithic language's, and the modules follow
-- Renata Shakirova's pairs language.
module DependentTypes
  ( -- * Terms
    Sig
  , Elaborated
  , Raw
  , Value
  , unannotated
  , universe
  , unitType
    -- * Contexts of types
  , HasTypes (..)
  , Typing
  , emptyTyping
  , typeOf
  , codomainAt
    -- * Normalisation
  , eval
  , nf
  , whnf
  , convertible
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Control.Monad.Free.Foil.Annotated (AnnSig (..))
import Data.Bifunctor (bimap)
import FreeFoil.NbE (Eval (..), Extend (..), HasDefinitions (..), HasHeads (..), NoContext (..))
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import DependentTypes.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | The signature of elaborated terms.
type Sig = AnnSig Maybe TermSig

-- | Elaborated terms in scope @n@.
type Elaborated n = AST FFPattern Sig n

-- | Terms as parsed, before elaboration.
type Raw n = FFTerm n

-- | Semantic values.
type Value = NbE.Value FFPattern Sig

-- | A term without its annotations.
unannotated :: Elaborated n -> Raw n
unannotated = hoistAST (\(AnnSig _ node) -> node)

-- | Terms print without their annotations.
instance Show (AST FFPattern Sig n) where
  show = show . unannotated

-- | The universe, whose type is itself.
universe :: Value n
universe = NbE.VNode (AnnSig Nothing UniverseSig)

-- | The unit type.
unitType :: Value n
unitType = NbE.VNode (AnnSig Nothing UnitSig)

-- * Contexts of types

-- | What the language needs of a context: the types of names.
class HasTypes ctx where
  -- | The context under a binder of one name of a type.
  assume :: DExt n l => NameBinder n l -> Value n -> ctx n -> ctx l
  -- | The type of a name, if the context knows it.
  typeOfName :: ctx n -> Name n -> Maybe (Value n)

-- | No types, so normalisation is untyped, except for the types in the
-- annotations.
instance HasTypes NoContext where
  assume _ _ _ = NoContext
  typeOfName _ _ = Nothing

-- | A type for every name in scope.
newtype Typing n = Typing (NameMap n (Value n))

-- | The context of the empty scope.
emptyTyping :: Typing VoidS
emptyTyping = Typing emptyNameMap

-- | The type of a name.
typeOf :: Name n -> Typing n -> Value n
typeOf x (Typing types) = lookupName x types

instance HasTypes Typing where
  assume x ty (Typing types) = Typing (addNameBinder x (sink ty) (sink1 types))
  typeOfName (Typing types) x = Just (lookupName x types)

instance HasDefinitions Typing FFPattern Sig where
  contextDefinition _ _ = NbE.VVar

-- * Rules

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> Typing o -> Substitution Value i o -> Elaborated i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Typing n -> Value n -> Elaborated n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> Typing n -> Value n -> Value n -> Bool #-}

-- | The heads are the function of an application and the scrutinee of
-- @split@, which η-expansion leaves alone.
instance HasHeads TermSig where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    AppSig fun arg     -> AppSig (hd fun) (other arg)
    SplitSig p ty body -> SplitSig (hd p) (other ty) body
    node               -> bimap id other node

-- | β for functions and for @split@ of a pair, the types of bound names,
-- and η at the types of introduction forms.
instance (HasTypes ctx, HasDefinitions ctx FFPattern Sig) => Eval ctx FFPattern Sig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env (AnnSig ann node) = case node of
    AppSig fun arg ->
      appValue (fmap (NbE.eval scope ctx env) ann) scope ctx (NbE.eval scope ctx env fun) (NbE.eval scope ctx env arg)
    SplitSig p ty (ScopedAST pat body) ->
      case NbE.eval scope ctx env p of
        NbE.VNode (AnnSig _ (PairSig a b)) -> case pat of
          FFPatternPair x y -> case assertDistinct (FFPatternPair x y) of
            Distinct -> NbE.eval scope ctx (addSubst (addSubst env x a) y b) body
          FFPatternVar _ -> error "DependentTypes: split binds two names"
        p' -> NbE.VSuspended env
                (AnnSig (fmap (NbE.eval scope ctx env) ann)
                  (SplitSig p' (NbE.eval scope ctx env ty) (ScopedAST pat body)))
    _ -> NbE.evalNode scope ctx env (AnnSig ann node)

  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term (AnnSig ann node) = AnnSig (fmap term ann) $ case node of
    LamSig dom body    -> LamSig (term dom) (scoped body (assumeVar dom))
    PiSig dom body     -> PiSig (term dom) (scoped body (assumeVar dom))
    SigmaSig dom body  -> SigmaSig (term dom) (scoped body (assumeVar dom))
    SplitSig p ty body -> SplitSig (term p) (term ty) (scoped body (assumeComponents ty))
    AppSig fun arg     -> AppSig (term fun) (term arg)
    PairSig a b        -> PairSig (term a) (term b)
    UniverseSig        -> UniverseSig
    UnitSig            -> UnitSig
    TTSig              -> TTSig

  {-# INLINABLE refineVar #-}
  refineVar scope ctx x = case typeOfName ctx x of
    Just ty -> expandAt scope ctx (NbE.VVar x) ty
    Nothing -> NbE.VVar x

  {-# INLINABLE refineSig #-}
  refineSig scope ctx value (AnnSig ann node) = case (ann, node) of
    (Just ty, AppSig {})   -> expandAt scope ctx value ty
    (Just ty, SplitSig {}) -> expandAt scope ctx value ty
    _                      -> value

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application of the type in the annotation.
appValue ::
  (Eval ctx FFPattern Sig, Distinct n) =>
  Maybe (Value n) -> Scope n -> ctx n -> Value n -> Value n -> Value n
{-# INLINE appValue #-}
appValue ann scope ctx fun arg = case fun of
  NbE.VSuspended env (AnnSig _ (LamSig _ (ScopedAST (FFPatternVar x) body))) ->
    case assertDistinct x of
      Distinct -> NbE.eval scope ctx (addSubst env x arg) body
  _ -> NbE.VNode (AnnSig ann (AppSig fun arg))

-- | The binder of one name of a type.
assumeVar :: HasTypes ctx => Value n -> Extend ctx FFPattern Sig n
assumeVar ty = Extend $ \_ pat _ ctx -> case pat of
  FFPatternVar x    -> assume x ty ctx
  FFPatternPair _ _ -> error "DependentTypes: this binder binds one name"

-- | The binder of @split p : (a : A) * B as (x, y) in t@: @x : A@, then
-- @y : B@ at @x@.
assumeComponents :: HasTypes ctx => Value n -> Extend ctx FFPattern Sig n
assumeComponents ty = Extend $ \scope pat _ ctx -> case pat of
  FFPatternPair x y -> case (assertDistinct x, assertExt x, assertExt y) of
    (Distinct, Ext, Ext) ->
      let ctxX = assume x (firstComponent ty) ctx
      in assume y (codomainAt (extendScope x scope) ctxX (sink ty) (NbE.VVar (nameOf x))) ctxX
  FFPatternVar _ -> error "DependentTypes: split binds two names"
  where
    firstComponent = \case
      NbE.VSuspended _ (AnnSig _ (SigmaSig a _)) -> a
      _ -> error "DependentTypes: split of a value whose type is not a Σ"

-- | The codomain of a Π or Σ type at a value.
codomainAt :: forall ctx n. (Eval ctx FFPattern Sig, Distinct n) => Scope n -> ctx n -> Value n -> Value n -> Value n
codomainAt scope ctx ty arg = case ty of
  NbE.VSuspended env (AnnSig _ (PiSig _ (ScopedAST (FFPatternVar b) cod))) -> at env b cod
  NbE.VSuspended env (AnnSig _ (SigmaSig _ (ScopedAST (FFPatternVar b) cod))) -> at env b cod
  _ -> error "DependentTypes: not a Π or Σ type"
  where
    at :: forall i l. Distinct i => Substitution Value i n -> NameBinder i l -> Elaborated l -> Value n
    at env b cod = case assertDistinct b of
      Distinct -> NbE.eval scope ctx (addSubst env b arg) cod

-- | η-expand a neutral at its type.
expandAt :: (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n -> Value n
expandAt scope ctx value ty = case ty of
  NbE.VNode (AnnSig _ UnitSig) -> NbE.VNode (AnnSig Nothing TTSig)
  NbE.VSuspended _ (AnnSig _ (PiSig dom _)) -> expandFunction scope ctx value ty dom
  _ -> value

-- | A neutral @f : (x : A) -> B@ as the value of @\\(x : A). f x@, whose
-- application is annotated with @B@. The value of @f@ sits in the
-- environment under a fresh name @g@.
expandFunction ::
  (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) =>
  Scope n -> ctx n -> Value n -> Value n -> Value n -> Value n
expandFunction scope ctx fun ty dom =
  withFresh scope $ \g ->
    let scopeG = extendScope g scope
        ctxG = assume g ty ctx
    in withFresh scopeG $ \x ->
         let scopeX = extendScope x scopeG
             ctxX = assume x (sink dom) ctxG
             cod = NbE.quote scopeX ctxX (codomainAt scopeX ctxX (sinkPast x (sinkPast g ty)) (NbE.VVar (nameOf x)))
             body = Node (AnnSig (Just cod) (AppSig (Var (sink (nameOf g))) (Var (nameOf x))))
         in NbE.VSuspended (addSubst identitySubst g fun)
              (AnnSig Nothing (LamSig dom (ScopedAST (FFPatternVar x) body)))

-- | A value under a binder.
sinkPast :: DExt n l => NameBinder n l -> Value n -> Value l
sinkPast _ = sink

-- * Normalisation

-- | Evaluation in a context of types.
eval :: (Distinct o, Distinct i) => Scope o -> Typing o -> Substitution Value i o -> Elaborated i -> Value o
{-# INLINE eval #-}
eval = NbE.eval

-- | Normal form in a context of types.
nf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n
{-# INLINE nf #-}
nf = NbE.nf

-- | Weak-head normal form in a context of types.
whnf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n
{-# INLINE whnf #-}
whnf = NbE.whnf

-- | Convertibility in a context of types.
convertible :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n -> Bool
{-# INLINE convertible #-}
convertible = Conv.convertible
