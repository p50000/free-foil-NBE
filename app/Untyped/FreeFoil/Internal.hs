{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module Internal where

import Data.Bifunctor
import Data.Bifunctor.TH (deriveBifunctor)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Unsafe.Coerce
import System.Exit (exitFailure)
import Control.DeepSeq
import GHC.Generics (Generic)

--- Foil lib ----
type Id = Int
type RawName = Id
type RawScope = IntSet

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData

newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord)

newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord)

emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName id)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert id scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope | IntSet.null scope = 0
                   | otherwise = IntSet.findMax scope + 1

withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

unsafeEquals :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeEquals (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 == name2

unsafeLess :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeLess (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 < name2

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember i s = IntSet.member i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

-- Distinct constraints
class ExtEndo (n :: S)

class (ExtEndo n => ExtEndo l ) => Ext (n:: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

class Distinct (n :: S)
instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
data DistinctEvidence ( n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence ( n:: S) ( l :: S) where
  Ext :: Ext n l => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withFresh :: Distinct n => Scope n
  -> (forall l . DExt n l => NameBinder n l -> r ) -> r
withFresh scope cont = withFreshBinder scope (\binder ->
unsafeAssertFresh binder cont)

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed :: Distinct o => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName id) cont
  | IntSet.member id rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

-- generic sinking
concreteSink :: DExt n l => Expr n -> Expr l
concreteSink = unsafeCoerce

class Sinkable (e :: S -> *) where
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

extendRenaming :: (Name n -> Name n') -> NameBinder n l
  -> (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r ) -> r
extendRenaming _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

--- Free Foil Generic Subst --- 

data ScopedAST sig n where
  ScopedAST :: NameBinder n l -> AST sig l -> ScopedAST sig n

instance (forall l. NFData (AST sig l)) => NFData (ScopedAST sig n) where
  rnf (ScopedAST binder body) = rnf binder `seq` rnf body

data AST sig n where
  Var :: Name n -> AST sig n
  Node :: sig (ScopedAST sig n) (AST sig n) -> AST sig n

deriving instance (forall scope term. (Generic scope, Generic term) => Generic (sig scope term)) => Generic (AST sig n)
deriving instance (forall scope term. (NFData scope, NFData term) => NFData (sig scope term), forall scope term. (Generic scope, Generic term) => Generic (sig scope term)) => NFData (AST sig n)

-- Substitution
newtype Substitution (sig :: * -> * -> *) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (AST sig o))

lookupSubst :: Substitution sig i o -> Name i -> AST sig o
lookupSubst (UnsafeSubstitution env) (UnsafeName id) =
    case IntMap.lookup id env of
        Just ex -> ex
        Nothing -> Var (UnsafeName id)

identitySubst :: Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

addSubst :: Substitution sig i o -> NameBinder i i' -> AST sig o -> Substitution sig i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution (IntMap.insert id ex env)

addRename :: Substitution sig i o -> NameBinder i i' -> Name o -> Substitution sig i' o
addRename s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
    | otherwise = addSubst s b (Var n)

instance Bifunctor sig => Sinkable (Substitution sig i) where
  sinkabilityProof rename (UnsafeSubstitution env) =
    UnsafeSubstitution (fmap (sinkabilityProof rename) env)

instance Bifunctor sig => Sinkable (AST sig) where
  -- sinkabilityProof :: (Name n -> Name l) -> AST sig n -> AST sig l
  sinkabilityProof rename = \case
    Var name -> Var (rename name)
    Node node -> Node (bimap f (sinkabilityProof rename) node)
    where
      f (ScopedAST binder body) =
        extendRenaming rename binder $ \rename' binder' ->
          ScopedAST binder' (sinkabilityProof rename' body)

substitute
  :: (Bifunctor sig, Distinct o)
  => Scope o
  -> Substitution sig i o
  -> AST sig i
  -> AST sig o
substitute scope subst = \case
  Var name -> lookupSubst subst name
  Node node -> Node (bimap f (substitute scope subst) node)
  where
    f (ScopedAST binder body) =
      withRefreshed scope (nameOf binder) $ \binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body
        in ScopedAST binder' body'

--- NBE ---


--- FOIL example ---
--- to be user-defined ---
data Neutral n where
  NVar :: {-# UNPACK #-} !(Name n) -> Neutral n
  NApp :: Neutral n -> Value n -> Neutral n

data Value n where
  VClosure :: Substitution Value i o -> {-# UNPACK #-} !(NameBinder i l) -> Expr l -> Value o
  VNeutral :: Neutral n -> Value n
-----

---- Generify via freeFoil? ---
-- nsig is signature defined by language syntax?
data Value nsig n where 
  VClosure :: Substitution (VClosure nsig) i o -> nsig (ScopedAST nsig i) (Value nsig i) --> Value nsig o
  VNeutral :: nsig n -> Value n




-- TH example freefoil (i dont understand T-T) ---
data Closure pat sig n where
  VarC ::
    Name n -> Closure pat sig n
  Closure ::
    (Distinct n) => Substitution (Closure pat sig) n o -> -- Environment of captured variables.
    sig (ScopedAST pat sig n) (Closure pat sig n) ->
    Closure pat sig o

-- | Compose two substitutions under a given scope to produce a combined substitution.
composeSubst ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Foil.Substitution (Closure pat sig) k n ->
  Foil.Substitution (Closure pat sig) k o
composeSubst
  scope
  env@(UnsafeSubstitution outerMap)
  env'@(UnsafeSubstitution innerMap) =
    UnsafeSubstitution $
      IntMap.union
        (IntMap.map (substituteClosure scope env) innerMap)
        outerMap

-- | Perform substitution inside a closure using the given environment and scope.
substituteClosure ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Closure pat sig n ->
  Closure pat sig o
substituteClosure scope env (VarC x) =
  Foil.lookupSubst env x
substituteClosure scope env (Closure env' sig) =
  Closure (composeSubst scope env env') sig

-- | Quote a closure back into an AST node, using the provided evaluation function.
quote' ::
  (Distinct n, Bifunctor sig, HasNameBinder pat, CoSinkable pat) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
    Foil.Scope m ->
    Foil.Substitution (Closure pat sig) l m ->
    AST pat sig l ->
    Closure pat sig m
  ) ->
  Foil.Scope n ->
  Closure pat sig n ->
  AST pat sig n
quote' eval scope = \case
  VarC x -> Var x
  Closure (env :: Foil.Substitution (Closure pat sig) i n) node ->
    Node $
      bimap
        (quoteScoped eval scope env patternToNameBinder)
        (quote' eval scope . substituteClosure scope env)
        node




