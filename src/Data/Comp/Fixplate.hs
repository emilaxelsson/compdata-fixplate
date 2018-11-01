{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

-- | A modest replacement for the basic machinery in
-- [Compdata](https://hackage.haskell.org/package/compdata).
--
-- = Differences and limitations
--
-- === Deriving of type classes for base functors
--
-- Compdata's macros for deriving are replaced by similar macros from
-- [deriving-compat](https://hackage.haskell.org/package/deriving-compat). See
-- the documentation for 'defaultEqualF' and similar functions in the same
-- section.
--
-- === Co-products and injections
--
-- Compdata and Fixplate use different names for equivalent things. For this
-- reason, we export type and pattern synonyms to make the interface as similar
-- to Compdata's as possible.
--
-- Unfortunately, ':+:' is defined as left-associative in Fixplate, which means
-- that injections will look differently. For example, consider a compound base
-- functor @F `:+:` G `:+:` H@. Elements from @G@ are injected differently in
-- the two libraries:
--
-- @
-- Inr (Inl ...) -- Compdata
-- `InL` (`InR` ...) -- Fixplate
-- @
--
-- (Note also the difference in capitalization.)
--
-- === Smart constructors
--
-- There are no TemplateHaskell macros for making smart constructors, but the
-- operators from "Data.Composition" (re-exported by this module) take us a long
-- way towards the same goal. Consider the following base functors:
--
-- > data Add a        = Add a a          deriving (Functor)
-- > data IfThenElse a = IfThenElse a a a deriving (Functor)
--
-- Smart versions of these constructors can now be defined as follows:
--
-- @
-- (|+|) :: Add `:<:` f => `Term` f -> `Term` f -> `Term` f
-- (|+|) = `inject` `.:` Add
--
-- ite :: IfThenElse `:<:` f => `Term` f -> `Term` f -> `Term` f -> `Term` f
-- ite = `inject` `.:.` IfThenElse
-- @

module Data.Comp.Fixplate
  ( -- * Basic classes and operations on functors
    Eq1, EqF (..)
  , Show1, ShowF (..)
  , deriveEq1
  , deriveShow1
  , defaultEqualF
  , defaultShowsPrecF
  , eqMod

    -- * Compositional data types
  , Term
  , pattern Term
  , unTerm
  , (:&:)
  , pattern (:&:)
  , (:+:) (..)
  , (:<:) (..)
  , inject
  , project

    -- * Rendering
  , HideInj -- Just the type, because it shows up in some class contexts
  , showTerm
  , showTermU
  , drawTerm
  , drawTermU

    -- * Making smart constructors
  , (.:)
  , (.:.)
  , (.::)
  , (.::.)
  , (.:::)
  ) where

import Data.Composition ((.:), (.:.), (.::), (.::.), (.:::))
import Data.Eq.Deriving (deriveEq1)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq1 (..), Show1 (..), eq1, showsPrec1)
import Data.Generics.Fixplate.Base
  ( Ann(..)
  , EqF(..)
  , Hole(..)
  , Mu(..)
  , ShowF(..)
  , showF
  )
import qualified Data.Generics.Fixplate.Draw as Fixplate
import Data.Generics.Fixplate.Functor ((:+:) (..))
import Data.Generics.Fixplate.Morphisms (cata)
import Data.Generics.Fixplate.Traversals (restructure)
import Data.Tree (Tree (..))
import qualified Data.Tree.View as TreeView
import Text.Show.Deriving (deriveShow1)



--------------------------------------------------------------------------------
-- * Basic classes and operations on functors
--------------------------------------------------------------------------------

-- | Default implementation of 'equalF'
--
-- Use as follows:
--
-- @
-- data F = ...
--
-- `deriveEq1` ''F -- Requires TemplateHaskell
-- instance `EqF` F where `equalF` = `defaultEqualF`
-- @
defaultEqualF :: (Eq1 f, Eq a) => f a -> f a -> Bool
defaultEqualF = eq1

-- | Default implementation of 'showsPrecF'
--
-- Use as follows:
--
-- @
-- data F = ...
--
-- `deriveShow1` ''F -- Requires TemplateHaskell
-- instance `ShowF` F where `showsPrecF` = `defaultShowsPrecF`
-- @
defaultShowsPrecF :: (Show1 f, Show a) => Int -> f a -> ShowS
defaultShowsPrecF = showsPrec1

eqMod :: (EqF f, Functor f, Foldable f) => f a -> f b -> Maybe [(a, b)]
eqMod t u
  | fmap (const ()) t `equalF` fmap (const ()) u = Just args
  | otherwise = Nothing
  where
    args = toList t `zip` toList u



--------------------------------------------------------------------------------
-- * Compositional data types
--------------------------------------------------------------------------------

type Term = Mu

pattern Term :: f (Term f) -> Term f
pattern Term f = Fix f
{-# COMPLETE Term #-}

unTerm :: Term f -> f (Term f)
unTerm (Term f) = f

type f :&: a = Ann f a

pattern (:&:) :: f b -> a -> (f :&: a) b
pattern f :&: a = Ann a f
{-# COMPLETE (:&:) #-}

class f :<: g where
  inj :: f a -> g a
  prj :: g a -> Maybe (f a)

infix 7 :<:

instance {-# OVERLAPPABLE #-} f :<: f where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} f :<: f => f :<: (g :+: f) where
  inj = InR
  prj (InL _) = Nothing
  prj (InR f) = Just f

-- | Unlike standard Data Types à la Carte, this instance recurses into the left
-- term. This is due to the left-associativity of ':+:' in Fixplate.
instance {-# OVERLAPS #-} f :<: h => f :<: (h :+: g) where
  inj = InL . inj
  prj (InL h) = prj h
  prj (InR _) = Nothing

inject :: f :<: g => f (Term g) -> Term g
inject = Fix . inj

project :: f :<: g => Term g -> Maybe (f (Term g))
project = prj . unTerm



--------------------------------------------------------------------------------
-- * Tree rendering
--------------------------------------------------------------------------------

-- | Convert a 'Term' to a 'Tree'
toTree :: (Functor f, Foldable f) => Term f -> Tree (f Hole)
toTree = cata $ \f -> Node (const Hole <$> f) $ toList f

-- | Wrapper type with a 'ShowF' instance that does not show injections ('InL',
-- 'InR')
newtype HideInj f a = HideInj {unHideInj :: f a}
  deriving (Foldable, Functor, Traversable)

instance {-# OVERLAPPABLE #-}  ShowF f => ShowF (HideInj f) where
  showsPrecF p = showsPrecF p . unHideInj

instance {-# OVERLAPPING #-} (ShowF (HideInj f), ShowF (HideInj g)) =>
                             ShowF (HideInj (f :+: g)) where
  showsPrecF p (HideInj (InL f)) = showsPrecF p (HideInj f)
  showsPrecF p (HideInj (InR g)) = showsPrecF p (HideInj g)

data Hole' = Hole'

instance Show Hole' where
  show Hole' = "_"

-- | Represent a 'Term' as an ASCII drawing
showTerm :: (Functor f, Foldable f, ShowF (HideInj f)) => Term f -> String
showTerm = Fixplate.showTree . restructure HideInj

-- | Represent a 'Term' as a Unicode drawing
showTermU :: (Functor f, Foldable f, ShowF (HideInj f)) => Term f -> String
showTermU =
  TreeView.showTree . fmap (showF . HideInj . fmap (const Hole')) . toTree

-- | Display a 'Term' as an ASCII drawing
drawTerm :: (Functor f, Foldable f, ShowF (HideInj f)) => Term f -> IO ()
drawTerm = Fixplate.drawTree . restructure HideInj

-- | Display a 'Term' as a Unicode drawing
drawTermU :: (Functor f, Foldable f, ShowF (HideInj f)) => Term f -> IO ()
drawTermU = putStrLn . showTermU
