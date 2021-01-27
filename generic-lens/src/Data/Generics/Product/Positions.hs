{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Positions
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive positional product type getters and setters generically.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Positions
  ( -- *Lenses

    -- $setup
    HasPosition (..)
  , HasPosition' (..)
  , HasPosition_ (..)
  , HasPosition0 (..)

  , getPosition
  , setPosition
  ) where

import "generic-lens-core" Data.Generics.Internal.Void
import qualified "generic-lens-core" Data.Generics.Internal.VL.Lens as VL
import qualified "generic-lens-core" Data.Generics.Product.Internal.Positions as Core

import GHC.TypeLits   (Nat)

-- $setup
-- == /Running example:/
--
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> :set -XDeriveGeneric
-- >>> :set -XGADTs
-- >>> :set -XFlexibleContexts
-- >>> import GHC.Generics
-- >>> :m +Data.Generics.Internal.VL.Lens
-- >>> :m +Data.Function
-- >>> :{
-- data Human = Human
--   { name    :: String
--   , age     :: Int
--   , address :: String
--   }
--   deriving (Generic, Show)
-- human :: Human
-- human = Human "Tunyasz" 50 "London"
-- :}

-- |Records that have a field at a given position.
class HasPosition (i :: Nat) s t a b | s i -> a, t i -> b, s i b -> t, t i a -> s where
  -- |A lens that focuses on a field at a given position. Compatible with the
  --  lens package's 'Control.Lens.Lens' type.
  --
  --  >>> human ^. position @1
  --  "Tunyasz"
  --  >>> human & position @3 .~ "Berlin"
  --  Human {name = "Tunyasz", age = 50, address = "Berlin"}
  --
  --  === /Type errors/
  --
  --  >>> human & position @4 .~ "Berlin"
  --  ...
  --  ... The type Human does not contain a field at position 4
  --  ...
  position :: VL.Lens s t a b

class HasPosition_ (i :: Nat) s t a b where
  position_ :: VL.Lens s t a b

-- |Records that have a field at a given position.
--
-- The difference between 'HasPosition' and 'HasPosition_' is similar to the
-- one between 'Data.Generics.Product.Fields.HasField' and
-- 'Data.Generics.Product.Fields.HasField_'.
-- See 'Data.Generics.Product.Fields.HasField_'.
class HasPosition' (i :: Nat) s a | s i -> a where
  position' :: VL.Lens s s a a

-- |Records that have a field at a given position.
--
-- This class gives the minimal constraints needed to define this lens.
-- For common uses, see 'HasPosition'.
class HasPosition0 (i :: Nat) s t a b where
  position0 :: VL.Lens s t a b

-- |
-- >>> getPosition @2 human
-- 50
getPosition :: forall i s a. HasPosition' i s a => s -> a
getPosition = VL.view (position' @i)

-- |
-- >>> setPosition @2 60 human
-- Human {name = "Tunyasz", age = 60, address = "London"}
setPosition :: forall i s a. HasPosition' i s a => a -> s -> s
setPosition = VL.set (position' @i)

instance Core.Context' i s a => HasPosition' i s a where
  position' f s = VL.ravel (Core.derived' @i) f s
  {-# INLINE position' #-}

instance (Core.Context i s t a b , HasPosition0 i s t a b) => HasPosition i s t a b where
  position = position0 @i
  {-# INLINE position #-}

-- | See Note [Uncluttering type signatures]
-- >>> :t position
-- position
--   :: (HasPosition i s t a b, Functor f) => (a -> f b) -> s -> f t
instance {-# OVERLAPPING #-} HasPosition f (Void1 a) (Void1 b) a b where
  position = undefined

instance (Core.Context_ i s t a b, HasPosition0 i s t a b) => HasPosition_ i s t a b where
  position_ = position0 @i
  {-# INLINE position_ #-}

instance {-# OVERLAPPING #-} HasPosition_ f (Void1 a) (Void1 b) a b where
  position_ = undefined

instance Core.Context0 i s t a b => HasPosition0 i s t a b where
  position0 f s = VL.ravel (Core.derived0 @i) f s
  {-# INLINE position0 #-}
