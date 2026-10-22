{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
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
--
-- A language's signature must be a 'Bifunctor' and a 'Bifoldable', both
-- derivable, and representational in both parameters (see 'evalNode'). Its
-- binder type must be 'Foil.CoSinkable', which free-foil generates, plus
-- 'Foil.SinkableK' for 'whnf', which has a generic default.
--
-- A language specialises 'nf', 'eval' and 'quote' to its types, next to
-- its 'Eval' instance, keeping the scope polymorphic:
--
-- > type Term n = AST Pattern TermSig n
-- > type Value n = NbE.Value Pattern TermSig n
-- >
-- > {-# SPECIALIZE NbE.nf    :: Distinct n => Scope n -> Term n -> Term n #-}
-- > {-# SPECIALIZE NbE.eval  :: (Distinct o, Distinct i) =>
-- >       Scope o -> Substitution Value i o -> Term i -> Value o #-}
-- > {-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Value n -> Term n #-}
--
-- and likewise 'FreeFoil.NbE.Conversion.conv' and
-- 'FreeFoil.NbE.Conversion.convertible'. Without the pragmas the monolithic
-- demonstration language is 1.25× to 1.4× slower: GHC's own specialisation
-- at a call site fixes the scope too, so it ends at the first binder, and it
-- never specialises the calls to 'eval' inside the instance.
module FreeFoil.NbE
  ( -- * Semantic domain
    Value
  , Whnf
  , Value' (VVar, VNode, VSuspended, Stuck)
  , vnode
  , vsuspended
    -- * Evaluation
  , Eval (..)
  , eval
  , evalNode
  , eliminate
  , force
    -- * Readback
  , quote
  , quoteScoped
  , nf
  , quoteWhnf
  , freezeScoped
  , whnf
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Substitution (..))
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..), substitute)
import           Data.Bifoldable             (Bifoldable (..))
import           Data.Bifunctor              (Bifunctor (..))
import qualified Data.IntMap                 as IntMap
import           Data.Monoid                 (Any (..))
import           Data.Void                   (Void, absurd)
import           GHC.Exts                    (inline)
import           Data.Coerce                 (coerce)
import           Unsafe.Coerce               (unsafeCoerce)

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

-- | The synonyms match a 'Whnf' as the 'Value' it was cast from, so that a
-- rule's case scrutinises the same variable as the case in 'eliminate' and
-- GHC merges the two.
fromWhnf :: Whnf binder sig n -> Value binder sig n
{-# INLINE fromWhnf #-}
fromWhnf = coerce

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

-- * Evaluation

-- | The elimination rules of a language. An eliminator evaluates its
-- principal subterm and matches the value through 'eliminate', as β does in
-- "LambdaPi":
--
-- > evalSig scope env = \case
-- >   AppSig fun arg ->
-- >     NbE.eliminate (eval scope env fun) $ \case
-- >       NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
-- >         case assertDistinct binder of
-- >           Distinct -> eval scope (addSubst env' binder (eval scope env arg)) body
-- >       NbE.Stuck fun' -> NbE.vnode (AppSig fun' (eval scope env arg))
-- >   node -> NbE.evalNode scope env node
--
-- Every other node falls through to 'evalNode'. The node arrives raw, so that
-- a redex never builds the interpreted node it would discard. The instance
-- upholds the 'Value' invariant, and it comes with the @SPECIALIZE@ pragmas
-- shown in the module header.
class (Bifunctor sig, Bifoldable sig) => Eval binder sig where
  evalSig ::
    (Foil.Distinct o, Foil.Distinct i) =>
    Foil.Scope o ->
    Foil.Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig = evalNode

-- | Evaluate a term under an environment: look variables up, hand nodes to
-- 'evalSig'. A variable that the environment does not map is a neutral.
eval ::
  (Eval binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  Foil.Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval scope !env = \case
  Var x -> Foil.lookupSubst env x
  Node node -> evalSig scope env node

-- | Evaluate a node that has no elimination rule: suspend it whole under the
-- environment if it has scoped subterms, otherwise evaluate its term
-- subterms. The same environment both suspends the node and drives its
-- subterms. A node with no subterms of one kind is reused by coercion, which
-- requires the signature to be representational in both parameters; every
-- ordinary data type is.
evalNode ::
  (Eval binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  Foil.Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
{-# INLINE evalNode #-}
evalNode scope env node =
  case ensureBivacuousFirst node of
    Just node' -> VNode_ (bimap absurd (eval scope env) node')
    Nothing -> VSuspended_ env $ case ensureBivacuousSecond node of
      -- Nothing to evaluate either (a lambda, say): reuse the cell as it is.
      Just node' -> vacuous node'
      Nothing    -> bimap id (eval scope env) node

-- A node whose parameter positions are provably empty is the same heap
-- object at any parameter type, so it is reused by coercion rather than
-- rebuilt field by field. The coercions are sound because a signature
-- bifunctor is representational in its parameters; the emptiness tests
-- constant-fold per constructor in specialised code.

vacuous :: f Void -> f a
vacuous = unsafeCoerce

ensureBivacuousFirst :: Bifoldable f => f a b -> Maybe (f Void b)
{-# INLINE ensureBivacuousFirst #-}
ensureBivacuousFirst x
  | getAny (bifoldMap (const (Any True)) (const (Any False)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

ensureBivacuousSecond :: Bifoldable f => f a b -> Maybe (f a Void)
{-# INLINE ensureBivacuousSecond #-}
ensureBivacuousSecond x
  | getAny (bifoldMap (const (Any False)) (const (Any True)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

-- * Readback

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

-- | Read a value back into a term. Term subterms recurse directly; scoped
-- subterms are read back under their binder by 'quoteScoped'. A glued value
-- is read back unfolded.
--
-- Every constraint here is used. An unused dictionary would make GHC split
-- 'quote' into a wrapper and a worker, and a @SPECIALIZE@ pragma would then
-- specialise only the wrapper.
quote ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote scope = \case
  VVar_ x -> Var x
  VNode_ node -> Node $! bimap absurd (quote scope) node
  VSuspended_ env node -> Node $! bimap (quoteScoped scope env) (quote scope) node
  VGlued_ _ unfolded -> quote scope unfolded

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the captured environment with it as a fresh neutral, evaluate the
-- body once under that environment, and quote the result. It inlines into
-- 'quote', so it is specialised with it.
quoteScoped ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
{-# INLINE quoteScoped #-}
quoteScoped scope env (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct -> ScopedAST binder' (quote scope' (eval scope' (extendEnv env) body))

-- | Normal form: evaluate, then read back fully.
nf ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nf #-}
nf scope = quote scope . eval scope Foil.identitySubst

-- | Read back the head of a value only: quote its term subterms, which are
-- values already, and freeze its scoped subterms instead of normalising under
-- their binders.
quoteWhnf ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf scope = \case
  VVar_ x -> Var x
  VNode_ node -> Node $ bimap absurd (quote scope) node
  VSuspended_ env node -> Node $ bimap (freezeScoped scope env) (quote scope) node
  VGlued_ _ unfolded -> quoteWhnf scope unfolded

-- | Freeze one scoped subterm of a suspended node without evaluating under
-- its binder: refresh the binder and substitute the captured environment,
-- quoted to terms, into the still-syntactic body. 'substitute' only renames,
-- so a redex under the binder survives.
freezeScoped ::
  (Eval binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeScoped scope env (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendSubst binder' scope' ->
    ScopedAST binder' (substitute scope' (extendSubst (quoteSubst scope env)) body)

-- | Quote every value in an environment, turning it into a syntactic
-- substitution.
quoteSubst ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  Foil.Substitution (Value binder sig) i n ->
  Foil.Substitution (AST binder sig) i n
quoteSubst scope (Foil.UnsafeSubstitution m) =
  Foil.UnsafeSubstitution (IntMap.map (quote scope) m)

-- | Weak-head normal form: evaluate, then read back the head only. Shares
-- 'eval' with 'nf'; 'quoteWhnf' does not go under binders, so a redex
-- under a lambda survives. Term positions are values already, so the two
-- readbacks differ only at scoped positions.
whnf ::
  (Eval binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  AST binder sig n ->
  AST binder sig n
whnf scope = quoteWhnf scope . eval scope Foil.identitySubst
