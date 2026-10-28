{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}
-- The Eval instance for an annotated signature is an orphan on purpose: it
-- belongs with 'EvalF', which the core does not know.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Evaluation of annotated terms ("Control.Monad.Free.Foil.Annotated") that
-- ignores the annotations. A language whose rules are written as 'EvalF'
-- evaluates terms over @t'AnnSig' ann sig@ with those rules: a node is read
-- past its annotation, and a value node carries the 'blank' annotation of
-- its type, since evaluation builds values, not source nodes. So the normal
-- form of an annotated term is annotated blank throughout, while the bodies
-- that 'FreeFoil.NbE.whnf' freezes keep their annotations, since they stay
-- syntax. Conversion checking is as blind to annotations as the annotation's
-- 'Data.ZipMatchK.ZipMatchK' and 'Data.ZipMatchK.ZipMatchFoldK' instances,
-- see "Control.Monad.Free.Foil.Annotated".
module FreeFoil.NbE.Annotated
  ( Annotation (..)
  , ignoring
  , unannotated
  ) where

import           Control.Monad.Free.Foil           (AST, hoistAST)
import           Control.Monad.Free.Foil.Annotated (AnnSig (..))
import           Data.Bifunctor                    (Bifunctor)

import           FreeFoil.NbE                      (Eval (..))
import           FreeFoil.NbE.Sum                  (EvalF (..), Inj (..))

-- | An annotation with a blank, for the nodes that evaluation builds.
class Annotation ann where
  blank :: ann t

-- | The position of a signature inside its annotated signature: a node is
-- recognised past its annotation and built with the 'blank' one.
ignoring :: Annotation ann => Inj sig (AnnSig ann sig)
{-# INLINE ignoring #-}
ignoring = Inj (AnnSig blank) (\(AnnSig _ node) -> Just node)

-- | The rules of a language, ignoring the annotations of its terms.
instance (EvalF binder sig, Annotation ann, Functor ann) => Eval binder (AnnSig ann sig) where
  {-# INLINE evalSig #-}
  evalSig scope env (AnnSig _ node) = evalF ignoring scope env node
  {-# INLINE etaMatchWith #-}
  etaMatchWith scoped term (AnnSig _ node) = AnnSig blank <$> etaMatchWithF ignoring scoped term node

-- | A term without its annotations.
unannotated :: (Functor ann, Bifunctor sig) => AST binder (AnnSig ann sig) n -> AST binder sig n
unannotated = hoistAST (\(AnnSig _ node) -> node)
