{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE ViewPatterns          #-}
-- | Normalisation by evaluation, generic in the signature of the object
-- language. A language is a signature bifunctor @sig@ and a binder type, as
-- in "Control.Monad.Free.Foil"; to normalise its terms it supplies one 'Eval'
-- instance, its elimination rules. The semantic domain ('Value'), evaluation
-- ('eval'), readback ('quote') and the normalisers 'nf' and 'whnf' are
-- generic.
--
-- The normaliser is untyped and intensional: it decides β and the language's
-- own reductions, not η, and it keeps one signature for terms and values, so
-- neutral and normal values are not told apart by type (see 'Value').
-- Conversion checking adds η for the introduction forms a language describes
-- with 'etaMatchWith'. With 'relateWith' a language may also make it a
-- check of subtyping.
--
-- A language's signature must be a 'Bifunctor' and a 'Bifoldable', both
-- derivable, and representational in both parameters (see 'evalNode'). It
-- names its heads in a 'HasHeads' instance, which may be empty. Its
-- binder type must be 'Foil.CoSinkable', which free-foil generates, plus
-- 'Foil.SinkableK' for 'whnf', which has a generic default.
--
-- Evaluation, readback and conversion take the scope and, beside it, a
-- context the client supplies. The core is polymorphic in the context, and a
-- language states in its 'Eval' instance what it needs of it. A context may
-- give the free names of a language values ('definition', by default from
-- 'HasDefinitions'). Under a binder the language says what the context
-- learns ('extendScopedWith'). By default the binder only adds its names, so
-- any 'Foil.Sinkable' context works with any language. In readback the
-- language may refine values by the context ('refineVar', 'refineSig'),
-- for example η-expand them at their types. The demonstration
-- languages use 'NoContext', which knows nothing beyond the scope.
--
-- A language specialises 'nf', 'eval' and 'quote' to its types, next to
-- its 'Eval' instance, keeping the scope polymorphic and fixing the context
-- to 'NoContext':
--
-- > type Term n = AST Pattern TermSig n
-- > type Value n = NbE.Value Pattern TermSig n
-- >
-- > {-# SPECIALIZE NbE.nf    :: Distinct n => Scope n -> NoContext n -> Term n -> Term n #-}
-- > {-# SPECIALIZE NbE.eval  :: (Distinct o, Distinct i) =>
-- >       Scope o -> NoContext o -> Substitution Value i o -> Term i -> Value o #-}
-- > {-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> NoContext n -> Value n -> Term n #-}
--
-- and likewise 'FreeFoil.NbE.Conversion.conv' and
-- 'FreeFoil.NbE.Conversion.convertible'. Without the pragmas the monolithic
-- demonstration language is 1.25× to 1.4× slower: GHC's own specialisation
-- at a call site fixes the scope too, so it ends at the first binder, and it
-- never specialises the calls to 'eval' inside the instance.
--
-- A client with a context of its own gives the same pragmas at its context.
-- For them to reach the rules, the instance marks 'evalSig' @INLINABLE@,
-- and 'etaMatchWith', 'extendScopedWith' and 'relateWith', if it gives
-- them, @INLINE@, as well as 'headsWith' of its 'HasHeads' instance.
-- Otherwise every node runs the unspecialised evaluator, and conversion and
-- readback build the nodes these two methods return. A helper of the
-- language that takes the context, such as lambda-pi's @appValue@, is
-- @INLINE@ too, so that it is specialised with the rules at every context.
module FreeFoil.NbE
  ( -- * Semantic domain
    Value
  , Whnf
  , Value' (VVar, VNode, VSuspended, Stuck)
  , vvar
  , vnode
  , vsuspended
    -- * Context
  , NoContext (..)
  , HasDefinitions (..)
  , Extend (..)
  , sinkExtend
    -- * Evaluation
  , HasHeads (..)
  , Eval (..)
  , relateNodes
  , relateExtended
  , eval
  , evalNode
  , eliminate
  , force
    -- * η
  , EtaTerm (..)
  , EtaScoped (..)
    -- * Readback
  , refine
  , quote
  , quoteScoped
  , nf
  , quoteWhnf
  , freezeScoped
  , whnf
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Name (..), Substitution (..))
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..), substitute)
import           Control.Monad.Free.Foil.Annotated (AnnSig (..))
import           Data.Bifoldable             (Bifoldable (..))
import           Data.Bifunctor              (Bifunctor (..))
import           Data.Bifunctor.Sum          (Sum (..))
import           Data.Coerce                 (coerce)
import qualified Data.IntMap                 as IntMap
import           Data.Monoid                 (Any (..))
import           Data.Void                   (Void, absurd)
import           Data.ZipMatchK              (ZipMatchFoldK, zipMatchFold2)
import           GHC.Exts                    (inline)

import           FreeFoil.NbE.Internal.Value

-- * Semantic domain

-- | A neutral variable.
pattern VVar :: Foil.Name n -> Whnf binder sig n
pattern VVar x <- (fromWhnf -> VVar_ x)

-- | A node without scoped subterms.
pattern VNode :: sig Void (Value binder sig n) -> Whnf binder sig n
pattern VNode node <- (fromWhnf -> VNode_ node)

-- | A node with scoped subterms, suspended under its environment.
pattern VSuspended ::
  () => Foil.Distinct i =>
  Foil.Substitution (Value binder sig) i n ->
  sig (ScopedAST binder sig i) (Value binder sig n) ->
  Whnf binder sig n
pattern VSuspended env node <- (fromWhnf -> VSuspended_ env node)

{-# COMPLETE VVar, VNode, VSuspended #-}

-- | Any head, as a value: the stuck case of a rule.
pattern Stuck :: Value binder sig n -> Whnf binder sig n
pattern Stuck v <- (fromWhnf -> v)

{-# COMPLETE Stuck #-}

-- | The synonyms match a 'Whnf' as the 'Value' it was cast from.
fromWhnf :: Whnf binder sig n -> Value binder sig n
{-# INLINE fromWhnf #-}
fromWhnf = coerce

-- | A neutral variable, as a value.
vvar :: Foil.Name n -> Value binder sig n
{-# INLINE vvar #-}
vvar = VVar_

-- | A node without scoped subterms, as a value.
vnode :: sig Void (Value binder sig n) -> Value binder sig n
{-# INLINE vnode #-}
vnode = VNode_

-- | A node with scoped subterms suspended under an environment, as a value.
vsuspended ::
  Foil.Distinct i =>
  Foil.Substitution (Value binder sig) i n ->
  sig (ScopedAST binder sig i) (Value binder sig n) ->
  Value binder sig n
{-# INLINE vsuspended #-}
vsuspended = VSuspended_

-- * Context

-- | The context that knows nothing beyond the scope.
data NoContext (n :: Foil.S) = NoContext

instance Foil.Sinkable NoContext where
  sinkabilityProof _ NoContext = NoContext

-- | The values a context gives to free names, the default of 'definition',
-- and the side of a glued value that readback follows, the default of
-- 'unfolding'. 'NoContext' defines nothing. A language generic in the
-- context requires this class of it in its 'Eval' instance, which needs
-- @UndecidableInstances@.
class HasDefinitions ctx binder sig where
  -- | The value of a free name, or the name itself if the context does not
  -- define it. A defined name may be glued to its value, so that readback
  -- and conversion can keep it folded.
  contextDefinition :: Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n

  -- | The side of a glued value that readback follows, from the folded and
  -- the unfolded side. By default the unfolded one.
  contextUnfolding :: Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n -> Value binder sig n
  {-# INLINE contextUnfolding #-}
  contextUnfolding _ _ _ unfolded = unfolded

instance HasDefinitions NoContext binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ _ = vvar

-- | The context under the binder of a scoped position: from the scope, the
-- binder, refreshed for the scope, the scope under it, which free-foil
-- computes when it refreshes the binder, and the context. A language gives
-- one for each scoped position of a node with 'extendScopedWith'. The
-- extension receives the language's 'Eval' instance from the core, so that
-- an instance whose extension evaluates does not refer to itself, and its
-- 'extendScopedWith' stays inlinable.
newtype Extend ctx binder sig n = Extend
  (forall l. (Eval ctx binder sig, Foil.Distinct n, Foil.DExt n l) =>
    Foil.Scope n -> binder n l -> Foil.Scope l -> ctx n -> ctx l)

-- | The context under a binder that adds nothing but its names: the same
-- context, sunk.
sinkExtend :: Foil.Sinkable ctx => Extend ctx binder sig n
{-# INLINE sinkExtend #-}
sinkExtend = Extend (\_ _ _ -> Foil.sink)

-- * η

-- | The observer of a term position of an introduction form: the eliminator
-- of that position, from the scope, the context and any value to the
-- component. The two observers of a pair are @fst@ and @snd@. Like an
-- 'Extend', an observer receives the language's 'Eval' instance from the
-- core, with a distinct scope, so that it may evaluate.
newtype EtaTerm ctx binder sig n =
  EtaTerm ((Eval ctx binder sig, Foil.Distinct n) => Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n)

-- | The observer of a scoped position of an introduction form: from the
-- context under the position's refreshed binder, that binder, and the other
-- value sunk into that scope, the eliminator applied to the names the binder
-- binds. The observer of a lambda's body applies the other value to the
-- bound name. The outer scope is distinct so that an observer may list the
-- binder's names.
newtype EtaScoped ctx binder sig n =
  EtaScoped
    (forall l. (Eval ctx binder sig, Foil.Distinct n, Foil.DExt n l) =>
      Foil.Scope l -> ctx l -> binder n l -> Value binder sig l -> Value binder sig l)

-- * Heads

-- | The heads of a signature's nodes: the term positions an elimination
-- rule eliminates, such as the function of an application. Readback and
-- conversion do not refine a head ('refine'), since η-expanding the
-- function of an application would make it a redex. A signature without
-- eliminators has no heads, which is the default:
--
-- > instance HasHeads TermSig
class Bifunctor sig => HasHeads sig where
  -- | The first function goes to the heads of a node, the second to every
  -- other term position:
  --
  -- > headsWith hd other = \case
  -- >   AppSig fun arg -> AppSig (hd fun) (other arg)
  -- >   node -> bimap id other node
  --
  -- Like 'extendScopedWith', the method is @INLINE@.
  headsWith :: (b -> d) -> (b -> d) -> sig a b -> sig a d
  {-# INLINE headsWith #-}
  headsWith _ other = bimap id other

-- | The heads of a sum are those of its summands.
instance (HasHeads f, HasHeads g) => HasHeads (Sum f g) where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    L2 node -> L2 (headsWith hd other node)
    R2 node -> R2 (headsWith hd other node)

-- | The heads of an annotated node are those of the node. An annotation is
-- not a head.
instance (Functor ann, HasHeads sig) => HasHeads (AnnSig ann sig) where
  {-# INLINE headsWith #-}
  headsWith hd other (AnnSig ann node) = AnnSig (fmap other ann) (headsWith hd other node)

-- * Evaluation

-- | A language becomes an NbE instance by giving its elimination rules. An
-- eliminator evaluates its principal subterm and matches the value through
-- 'eliminate', as β does in "LambdaPi":
--
-- > evalSig scope ctx env = \case
-- >   AppSig fun arg ->
-- >     NbE.eliminate (eval scope ctx env fun) $ \case
-- >       NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
-- >         case assertDistinct binder of
-- >           Distinct -> eval scope ctx (addSubst env' binder (eval scope ctx env arg)) body
-- >       NbE.Stuck fun' -> NbE.vnode (AppSig fun' (eval scope ctx env arg))
-- >   node -> NbE.evalNode scope ctx env node
--
-- Every other node falls through to 'evalNode'. The node arrives raw, so
-- that a redex never builds the interpreted node it would discard. The
-- instance upholds the 'Value' invariant, and it comes with the pragmas
-- described in the module header.
class (Bifunctor sig, Bifoldable sig, HasHeads sig) => Eval ctx binder sig where
  -- | The value of a free name, or the name itself if it has none. By
  -- default the context's 'contextDefinition'.
  definition :: Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n
  default definition :: HasDefinitions ctx binder sig => Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n
  {-# INLINE definition #-}
  definition = contextDefinition

  -- | The side of a glued value that readback follows, from the folded and
  -- the unfolded side. By default the context's 'contextUnfolding'.
  unfolding :: Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n -> Value binder sig n
  default unfolding :: HasDefinitions ctx binder sig => Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n -> Value binder sig n
  {-# INLINE unfolding #-}
  unfolding = contextUnfolding

  evalSig ::
    (Foil.Distinct o, Foil.Distinct i) =>
    Foil.Scope o ->
    ctx o ->
    Foil.Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig = evalNode

  -- | The η law of an introduction form, for conversion checking, in the
  -- style of 'Data.ZipMatchK.zipMatchWith2':
  --
  -- > etaMatchWith _ term = \case
  -- >   PairSig a b -> Just (PairSig (term a (EtaTerm (\_ _ -> fstValue))) (term b (EtaTerm (\_ _ -> sndValue))))
  -- >   _ -> Nothing
  --
  -- A constructor with an η law combines each of its positions with the
  -- position's observer, a t'EtaScoped' or a t'EtaTerm'. Any other
  -- constructor answers 'Nothing', the default. Whether the answer is a
  -- 'Just' depends only on the node, not on its subterms. A lambda observes
  -- its body by applying the other value to the bound name (Coquand 1996),
  -- a pair observes its components by the projections (Abel and Coquand
  -- 2007).
  etaMatchWith ::
    (a -> EtaScoped ctx binder sig n -> c) ->
    (b -> EtaTerm ctx binder sig n -> d) ->
    sig a b ->
    Maybe (sig c d)
  {-# INLINE etaMatchWith #-}
  etaMatchWith _ _ _ = Nothing

  -- | The context under the binder of each scoped position of a node, for
  -- readback and conversion, in the style of 'etaMatchWith':
  --
  -- > extendScopedWith scoped term = \case
  -- >   PiSig dom body -> PiSig (term dom) (scoped body (Extend (\_ (PatternVar x) _ ctx -> assume x dom ctx)))
  -- >   …
  --
  -- The term positions are values, so that an extension may use them, such
  -- as the domain of a Π. By default every binder only adds its names
  -- ('sinkExtend'), which needs a 'Foil.Sinkable' context. A context that
  -- holds something for every name in scope, such as its type, is not
  -- sinkable, and a language that uses one gives this method. The method is
  -- @INLINE@, so that readback and conversion build no intermediate node.
  extendScopedWith ::
    Foil.Distinct n =>
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    sig a (Value binder sig n) ->
    sig c d
  default extendScopedWith ::
    (Foil.Sinkable ctx, Foil.Distinct n) =>
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    sig a (Value binder sig n) ->
    sig c d
  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term = bimap (\a -> scoped a sinkExtend) term

  -- | How conversion compares two nodes of the same constructor, in the
  -- style of free-foil's 'Data.ZipMatchK.zipMatchFoldK': each pair of
  -- scoped positions under one binder, with the context under it, and each
  -- pair of term positions in a context of its own, a head ('headsWith') by
  -- the last function. 'Nothing' if the nodes do not match. A language whose
  -- context records the direction of the check makes conversion a check of
  -- subtyping, here with a contravariant domain:
  --
  -- > relateWith scope ctx scoped term hd l r = case (l, r) of
  -- >   (PiSig domL codL, PiSig domR codR) -> Just $
  -- >     term domL domR (flipped ctx) <> scoped codL codR (assumeVar (smaller ctx domL domR))
  -- >   (UniverseSig i, UniverseSig j) | below ctx i j -> Just mempty
  -- >   _ -> relateNodes scope ctx scoped term hd l r
  --
  -- By default every node is compared as by 'relateNodes'. The method is
  -- @INLINE@, like 'extendScopedWith'.
  relateWith ::
    (Monoid m, Foil.Distinct n) =>
    Foil.Scope n ->
    ctx n ->
    (a -> a' -> Extend ctx binder sig n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    sig a (Value binder sig n) ->
    sig a' (Value binder sig n) ->
    Maybe m
  default relateWith ::
    (ZipMatchFoldK sig, Monoid m, Foil.Distinct n) =>
    Foil.Scope n ->
    ctx n ->
    (a -> a' -> Extend ctx binder sig n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
    sig a (Value binder sig n) ->
    sig a' (Value binder sig n) ->
    Maybe m
  {-# INLINE relateWith #-}
  relateWith scope ctx scoped term hd l r = relateNodes scope ctx scoped term hd l r

  -- | Refine a variable by the context, in readback and conversion
  -- ('refine'). For example, a language whose context knows types
  -- η-expands @f@ of a function type to @λx. f x@. By default a variable
  -- stays as it is.
  --
  -- Unlike 'definition', which 'eval' asks once about a free name, the
  -- method sees every variable, bound ones too, in the context where it is
  -- read back.
  --
  -- The result upholds the invariant of 'Value' and contains the variable
  -- only at heads ('HasHeads'), as @f@ in @λx. f x@. Readback refines every
  -- other position again, so the variable anywhere else would be refined
  -- forever. The same holds for 'refineSig' and its node.
  --
  -- Like an 'Extend', the method receives the language's 'Eval' instance
  -- from the core, so that an instance that refines through other
  -- instances, as a sum of fragments does, does not refer to itself and
  -- stays inlinable.
  refineVar :: (Eval ctx binder sig, Foil.Distinct n) => Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n
  {-# INLINE refineVar #-}
  refineVar _ _ = vvar

  -- | Refine a node by the context, like 'refineVar'. The method sees the
  -- constructor and the term positions, but not the scoped ones. The value
  -- of the node comes first, to embed, as in @λx. f a x@. By default a node
  -- stays as it is.
  refineSig ::
    (Eval ctx binder sig, Foil.Distinct n) =>
    Foil.Scope n -> ctx n -> Value binder sig n -> sig a (Value binder sig n) -> Value binder sig n
  {-# INLINE refineSig #-}
  refineSig _ _ value _ = value

-- | The default of 'relateWith': two nodes match by free-foil's
-- 'ZipMatchFoldK', every scoped position extends the context as the left
-- node's 'extendScopedWith' says, and every term position keeps the context.
-- A language's own cases fall back on it:
--
-- > _ -> relateNodes scope ctx scoped term hd l r
relateNodes ::
  (Eval ctx binder sig, ZipMatchFoldK sig, Monoid m, Foil.Distinct n) =>
  Foil.Scope n ->
  ctx n ->
  (a -> a' -> Extend ctx binder sig n -> m) ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  sig a (Value binder sig n) ->
  sig a' (Value binder sig n) ->
  Maybe m
{-# INLINE relateNodes #-}
relateNodes _ ctx scoped term hd l r =
  relateExtended ctx term hd (extendScopedWith (\a extend a' -> scoped a a' extend) id l) r

-- | Compare two nodes position by position, if they match by free-foil's
-- 'ZipMatchFoldK': the scoped positions of the left node, already given
-- their extensions and as functions of the right ones, and the term
-- positions in the context, the heads ('headsWith') by the last function.
-- For a language that extends the context otherwise than 'extendScopedWith'
-- says, and for a fragment @f@ of a language @sig@.
relateExtended ::
  (HasHeads f, ZipMatchFoldK f, Monoid m) =>
  ctx n ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  (Value binder sig n -> Value binder sig n -> ctx n -> m) ->
  f (a' -> m) (Value binder sig n) ->
  f a' (Value binder sig n) ->
  Maybe m
{-# INLINE relateExtended #-}
relateExtended ctx term hd l r =
  zipMatchFold2 ($) ($) (headsWith (\v v' -> hd v v' ctx) (\v v' -> term v v' ctx) l) r

-- | Evaluate a term under an environment: look variables up, hand nodes to
-- 'evalSig'. A variable that the environment does not map is a free name,
-- which unfolds to its value if the context defines it and is a neutral
-- otherwise.
eval ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval scope ctx !env = \case
  -- Only a name the environment does not map goes to 'definition'. A name
  -- bound in the term never gets there: β maps it with 'Foil.addSubst', and
  -- readback and conversion refresh it against the output scope, so it is
  -- not mistaken for a defined name with the same raw name.
  Var x -> lookupSubstWith (definition scope ctx) id env x
  Node node -> evalSig scope ctx env node

-- | Look a name up in a substitution: its image, given to the second
-- function, if the substitution maps it, and otherwise the same name in the
-- output scope, given to the first. This is 'Foil.lookupSubst' with the
-- unmapped case left to the caller, and it relies on the same invariant
-- (Maclaurin, Radul and Paszke 2022, Definition 4.1): a name the
-- substitution does not map is a name of the scope where it started as
-- 'Foil.identitySubst', or a binder kept because it is fresh for the output
-- scope, so the output scope has the same name. The function belongs in
-- free-foil, where 'Foil.lookupSubst' is @lookupSubstWith injectName id@.
lookupSubstWith :: (Foil.Name o -> r) -> (e o -> r) -> Foil.Substitution e i o -> Foil.Name i -> r
{-# INLINE lookupSubstWith #-}
lookupSubstWith unmapped mapped (Foil.UnsafeSubstitution values) (Foil.UnsafeName name) =
  case IntMap.lookup name values of
    Just value -> mapped value
    Nothing    -> unmapped (Foil.UnsafeName name)

-- | Evaluate a node that has no elimination rule: suspend it whole under the
-- environment if it has scoped subterms, otherwise evaluate its term
-- subterms. The same environment both suspends the node and drives its
-- subterms.
--
-- The term subterms are always mapped, even when the signature's fold finds
-- none: an annotated signature ("Control.Monad.Free.Foil.Annotated") keeps
-- its annotation out of 'Bifoldable' but inside 'Bifunctor', so a λ whose
-- annotation is its type has terms to evaluate that no fold sees. Mapping a
-- node with no term subterms allocates no new node, since GHC's common
-- subexpression elimination on STG reuses the old one.
evalNode ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
{-# INLINE evalNode #-}
evalNode scope ctx env node
  | hasScoped = VSuspended_ env (bimap id (eval scope ctx env) node)
  | otherwise = VNode_ (bimap noScoped (eval scope ctx env) node)
  where
    -- Constant-folds per constructor in specialised code. An annotation
    -- holds no scoped subterms, so the fold sees all of them.
    hasScoped = getAny (bifoldMap (const (Any True)) (const (Any False)) node)
    noScoped _ = error "evalNode: a scoped subterm that (Bifoldable sig) does not see"

-- | Match the value of a principal subterm: an elimination rule sees it as a
-- 'Whnf', through the synonyms 'VVar', 'VNode', 'VSuspended' and 'Stuck'. On
-- a glued value the rule applies to both sides: the folded side is a
-- neutral, so the rule leaves it stuck, and the unfolded side may be glued
-- again. The results are glued again, so that readback can still choose. On
-- any other value the rule applies directly, and it is a closure only on a
-- glued value.
eliminate ::
  Value binder sig n ->
  (Whnf binder sig n -> Value binder sig n) ->
  Value binder sig n
{-# INLINE eliminate #-}
eliminate v rule = case v of
  VGlued_ folded unfolded -> VGlued_ (eliminateLoop folded rule) (eliminateLoop unfolded rule)
  _ -> inline rule (coerce v)

-- | The loop of 'eliminate' under the first glue, out of line.
eliminateLoop ::
  Value binder sig n ->
  (Whnf binder sig n -> Value binder sig n) ->
  Value binder sig n
{-# NOINLINE eliminateLoop #-}
eliminateLoop v rule = case v of
  VGlued_ folded unfolded -> VGlued_ (eliminateLoop folded rule) (eliminateLoop unfolded rule)
  _ -> rule (coerce v)

-- | The unfolded head of a value: peel every layer of glue off its root.
force :: Value binder sig n -> Whnf binder sig n
force = \case
  VGlued_ _ unfolded -> force unfolded
  v                  -> coerce v

-- * Readback

-- | Refine a value by the context: a variable by 'refineVar', a node by
-- 'refineSig'. A glued value stays as it is: readback and conversion refine
-- the side they follow.
refine ::
  (Eval ctx binder sig, Foil.Distinct n) =>
  Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n
{-# INLINE refine #-}
refine scope ctx value = case value of
  VVar_ x            -> refineVar scope ctx x
  VNode_ node        -> refineSig scope ctx value node
  VSuspended_ _ node -> refineSig scope ctx value node
  VGlued_ _ _        -> value

-- | Read a value back into a term. Term subterms recurse directly; scoped
-- subterms are read back under their binder by 'quoteScoped'. A glued value
-- is read back on the side the context chooses ('unfolding').
--
-- Every constraint here is used. An unused dictionary would make GHC split
-- 'quote' into a wrapper and a worker, and a @SPECIALIZE@ pragma would then
-- specialise only the wrapper.
quote ::
  forall ctx binder sig n.
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote scope ctx = \case
  VGlued_ folded unfolded -> quote scope ctx (unfolding scope ctx folded unfolded)
  value -> readHead scope ctx (refine scope ctx value)
  where
    -- Local, so that a specialisation of 'quote' covers it, and closed, so
    -- that no call allocates it.
    readHead :: Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> AST binder sig l
    readHead s c = readHeadWith (readHead s c) s c

-- | Read a value back without refining it: a head ('headsWith'), a value
-- refined already, or a value of an environment that 'freezeScoped'
-- substitutes. Its heads go to the first function, every other position to
-- 'quote'. 'quote' and 'quoteWhnf' pass the function itself.
readHeadWith ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  (Value binder sig n -> AST binder sig n) ->
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINE readHeadWith #-}
readHeadWith hd scope ctx = \case
  VVar_ x -> Var x
  VNode_ node -> Node $! bimap absurd id (headsWith hd (quote scope ctx) node)
  VSuspended_ env node ->
    Node $! headsWith hd (quote scope ctx) (extendScopedWith (quoteScoped scope ctx env) id node)
  VGlued_ folded unfolded -> hd (unfolding scope ctx folded unfolded)

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the context with the position's 'Extend' and the captured
-- environment with the binder, as a fresh neutral, evaluate the body once
-- under them, and quote the result. It inlines into 'quote', so it is
-- specialised with it.
quoteScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  Extend ctx binder sig n ->
  ScopedAST binder sig n
{-# INLINE quoteScoped #-}
quoteScoped scope ctx env (ScopedAST binder body) (Extend extend) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let ctx' = extend scope binder' scope' ctx
        in ScopedAST binder' (quote scope' ctx' (eval scope' ctx' (extendEnv env) body))

-- | Normal form: evaluate, then read back fully.
--
-- > nf (λf. (λg. λx. g x) f)  =  λf. λx. f x
--
-- The normal form is β-normal but not η-short. For example, @nf@ does not
-- contract @λx. f x@ to @f@, although 'FreeFoil.NbE.Conversion.conv'
-- identifies the two. Contraction can change the type of a term. In Rocq
-- the type of @f@ need not be convertible to the type of @λx. f x@, which is
-- why Rocq defines η-expansion but no η-reduction
-- (<https://rocq-prover.org/doc/master/refman/language/core/conversion.html#expansion Rocq reference manual, η-expansion>).
-- In Rzk an η-expanded witness of an extension type type-checks where the
-- contracted one does not (Kudasov, Sim and Ahrens,
-- /Rzk: a Proof Assistant for Synthetic ∞-Categories/, 2026, Remark 4.5,
-- <https://arxiv.org/abs/2607.12207>). So readback keeps the η-shape of the
-- term.
nf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  ctx n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nf #-}
nf scope ctx = quote scope ctx . eval scope ctx Foil.identitySubst

-- | Read back the head of a value only: quote its term subterms, which are
-- values already, and freeze its scoped subterms instead of normalising under
-- their binders.
quoteWhnf ::
  forall ctx binder sig n.
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf scope ctx value = case refine scope ctx value of
  VVar_ x -> Var x
  VNode_ node -> Node $ bimap absurd id (headsWith (readHead scope ctx) (quote scope ctx) node)
  VSuspended_ env node ->
    Node $ bimap (freezeScoped (readHead scope ctx) scope env) id (headsWith (readHead scope ctx) (quote scope ctx) node)
  VGlued_ folded unfolded -> quoteWhnf scope ctx (unfolding scope ctx folded unfolded)
  where
    -- As in 'quote', so that a specialisation of 'quoteWhnf' covers it.
    readHead :: Foil.Distinct l => Foil.Scope l -> ctx l -> Value binder sig l -> AST binder sig l
    readHead s c = readHeadWith (readHead s c) s c

-- | Freeze one scoped subterm of a suspended node without evaluating under
-- its binder: refresh the binder and substitute the captured environment,
-- read back to terms by the given function, into the still-syntactic body.
-- 'substitute' only renames, so a redex under the binder survives.
--
-- The body is not refined, so 'quoteWhnf' reads the environment back
-- without refining its values at the root. Otherwise an
-- η-expanded value would land at a head of the body: @f@ refined to
-- @λy. f y@ would freeze as @λx. (λy. f y) x@.
freezeScoped ::
  (Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.SinkableK binder, Bifunctor sig) =>
  (Value binder sig n -> AST binder sig n) ->
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeScoped readValue scope (Foil.UnsafeSubstitution env) (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendSubst binder' scope' ->
    ScopedAST binder' (substitute scope' (extendSubst (Foil.UnsafeSubstitution (IntMap.map readValue env))) body)

-- | Weak-head normal form: evaluate, then read back the head only. Shares
-- 'eval' with 'nf'; 'quoteWhnf' does not go under binders, so a redex
-- under a lambda survives. Term positions are values already, so the two
-- readbacks differ only at scoped positions.
whnf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  ctx n ->
  AST binder sig n ->
  AST binder sig n
whnf scope ctx = quoteWhnf scope ctx . eval scope ctx Foil.identitySubst
