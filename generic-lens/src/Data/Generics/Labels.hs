{-# LANGUAGE PackageImports #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wno-orphans        #-}

--------------------------------------------------------------------------------
-- |
-- Module      : Data.Generics.Labels
-- Copyright   : (C) 2020 Csongor Kiss
-- License     : BSD3
-- Maintainer  : Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides an (orphan) IsLabel instance for field lenses and constructor prisms.
-- Use at your own risk.
--------------------------------------------------------------------------------

module Data.Generics.Labels
  ( -- * Orphan IsLabel Instance
    -- $sec1
    Field(..)
  , Field'
  , Constructor(..)
  , Constructor'
  ) where

import "this" Data.Generics.Product
import "this" Data.Generics.Sum

import "generic-lens-core" Data.Generics.Internal.VL.Lens  (Lens)
import "this" Data.Generics.Internal.VL.Prism (Prism)

import Data.Profunctor    (Choice)
import Data.Type.Bool     (type (&&))
import Data.Type.Equality (type (==))

import GHC.OverloadedLabels
import GHC.TypeLits

-- $sec1
-- An instance for creating lenses and prisms with @#identifiers@ from the
-- @OverloadedLabels@ extension.  Note that since overloaded labels do not
-- support symbols starting with capital letters, all prisms (which come from
-- constructor names, which are capitalized) must be prefixed with an underscore
-- (e.g. @#_ConstructorName@).
--
-- Morally:
--
-- @
-- instance (HasField name s t a b) => IsLabel name (Lens s t a b) where ...
-- @
-- and
--
-- @
-- instance (AsConstructor name s t a b) => IsLabel name (Prism s t a b) where ...
-- @
--
-- Remember:
--
-- @
-- type Lens = forall f. Functor f => (a -> f b) -> s -> f t
--
-- type Prism s t a b = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)
-- @
--
-- The orphan instance is unavoidable if we want to work with
-- lenses-as-functions (as opposed to a 'ReifiedLens'-like newtype).

-- | 'Field' is morally the same as 'HasField', but it is constructed from an
-- incoherent combination of 'HasField' and 'HasField''.  In this way, it can be
-- seamlessly used in the 'IsLabel' instance even when dealing with data types
-- that don't have 'Field' instances (like data instances).
class Field name s t a b | s name -> a, t name -> b, s name b -> t, t name a -> s where
  fieldLens :: Lens s t a b

type Field' name s a = Field name s s a a

instance {-# INCOHERENT #-} HasField name s t a b => Field name s t a b where
  fieldLens = field @name

instance {-# INCOHERENT #-} HasField' name s a => Field name s s a a where
  fieldLens = field' @name

-- | 'Constructor' is morally the same as 'AsConstructor', but it is constructed from an
-- incoherent combination of 'AsConstructor' and 'AsConstructor''.  In this way, it can be
-- seamlessly used in the 'IsLabel' instance even when dealing with data types
-- that don't have 'Constructor' instances (like data instances).
class Constructor name s t a b | name s -> a, name t -> b where
  constructorPrism :: Prism s t a b

type Constructor' name s a = Constructor name s s a a

instance {-# INCOHERENT #-} AsConstructor name s t a b => Constructor name s t a b where
  constructorPrism = _Ctor @name

instance {-# INCOHERENT #-} AsConstructor' name s a => Constructor name s s a a where
  constructorPrism = _Ctor' @name

type family BeginsWithCapital (name :: Symbol) :: Bool where
  BeginsWithCapital name = CmpSymbol "_@" name == 'LT && CmpSymbol "_[" name == 'GT

instance ( capital ~ BeginsWithCapital name
         , IsLabelHelper capital name p f s t a b
         , pafb ~ p a (f b), psft ~ p s (f t)) => IsLabel name (pafb -> psft) where
  fromLabel = labelOutput @capital @name @p @f

-- | This helper class allows us to customize the output type of the lens to be
-- either 'Prism' or 'Lens' (by choosing appropriate @p@ and @f@) as well as to
-- choose between whether we're dealing with a lens or a prism.  The choice is
-- made by whether the @capital@ argument is true or false, which is determined by
-- whether the symbol starts with an underscore followed by a capital letter
-- (a check done in the 'IsLabel' instance above).  If so, then we're dealing
-- with a constructor name, which should be a prism, and otherwise, it's a field
-- name, so we have a lens.
class IsLabelHelper capital name p f s t a b where
  labelOutput :: p a (f b) -> p s (f t)

instance (Functor f, Field name s t a b) => IsLabelHelper 'False name (->) f s t a b where
  labelOutput = fieldLens @name

instance ( Applicative f, Choice p, Constructor name s t a b
         , name' ~ AppendSymbol "_" name) => IsLabelHelper 'True name' p f s t a b where
  labelOutput = constructorPrism @name
