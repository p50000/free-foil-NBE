{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
-- | The binders of the composed language: a pattern binds one name (a
-- lambda, a Pi) or two (@split@, the @suc@ branch of @natrec@). The fragments
-- themselves are polymorphic in the binder and extend an environment by
-- position with free-foil's 'addSubstPattern'; the language fixes the pattern
-- type. Two constructors in one pattern type exercise the shape check of
-- conversion checking, which a language with one binder shape never reaches.
module Fragments.Pattern
  ( Pat (..)
  ) where

import Control.DeepSeq    (NFData (rnf))
import Control.Monad.Foil
import Generics.Kind.TH   (deriveGenericK)

-- | A pattern that binds one or two names.
data Pat (n :: S) (l :: S) where
  PatVar  :: NameBinder n l -> Pat n l
  PatPair :: NameBinder n i -> NameBinder i l -> Pat n l

deriveGenericK ''Pat

instance SinkableK Pat
instance HasNameBinders Pat
instance UnifiablePattern Pat

instance NFData (Pat n l) where
  rnf (PatVar x)    = rnf x
  rnf (PatPair x y) = rnf x `seq` rnf y

-- | Written out, in the form that free-foil's @mkFreeFoil@ generates for a
-- binding type. The generic defaults go through the kind-generic
-- representation of the pattern at every binder, which conversion checking
-- and evaluation do at every lambda and every @split@.
instance CoSinkable Pat where
  coSinkabilityProof rename (PatVar x) cont =
    coSinkabilityProof rename x $ \rename' x' -> cont rename' (PatVar x')
  coSinkabilityProof rename (PatPair x y) cont =
    coSinkabilityProof rename x $ \rename' x' ->
      coSinkabilityProof rename' y $ \rename'' y' -> cont rename'' (PatPair x' y')

  withPattern withBinder _unit _comp scope (PatVar x) cont =
    withBinder scope x $ \f x' ->
      let scope' = extendScope x' scope
      in cont f (PatVar x') scope'
  withPattern withBinder _unit comp scope (PatPair x y) cont =
    withBinder scope x $ \f x' ->
      let scope' = extendScope x' scope
      in withBinder scope' y $ \g y' ->
           let scope'' = extendScope y' scope'
           in cont (comp f g) (PatPair x' y') scope''
  {-# INLINE withPattern #-}

  nameBinderListOf (PatVar x)    = NameBinderListCons x NameBinderListEmpty
  nameBinderListOf (PatPair x y) = NameBinderListCons x (NameBinderListCons y NameBinderListEmpty)
