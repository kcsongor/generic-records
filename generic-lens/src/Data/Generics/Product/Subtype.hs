{-# LANGUAGE PackageImports #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Subtype
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Structural subtype relationships between product types.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Subtype
  ( -- *Lenses
    --
    -- $setup
    Subtype (..)
  ) where


import "generic-lens-core" Data.Generics.Internal.Void
import qualified "generic-lens-core" Data.Generics.Internal.VL.Lens as VL
import qualified "generic-lens-core" Data.Generics.Product.Internal.Subtype as Core

import GHC.Generics (Generic (to, from) )

-- $setup
-- == /Running example:/
--
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> :set -XDeriveGeneric
-- >>> :set -XDuplicateRecordFields
-- >>> import GHC.Generics
-- >>> :m +Data.Generics.Internal.VL.Lens
-- >>> :{
-- data Human = Human
--   { name    :: String
--   , age     :: Int
--   , address :: String
--   }
--   deriving (Generic, Show)
-- data Animal = Animal
--   { name    :: String
--   , age     :: Int
--   }
--   deriving (Generic, Show)
-- human :: Human
-- human = Human "Tunyasz" 50 "London"
-- :}

-- |Structural subtype relationship
--
-- @sub@ is a (structural) `subtype' of @sup@, if its fields are a subset of
-- those of @sup@.
--
class Subtype sup sub where
  -- |Structural subtype lens. Given a subtype relationship @sub :< sup@,
  --  we can focus on the @sub@ structure of @sup@.
  --
  -- >>> human ^. super @Animal
  -- Animal {name = "Tunyasz", age = 50}
  --
  -- >>> set (super @Animal) (Animal "dog" 10) human
  -- Human {name = "dog", age = 10, address = "London"}
  super  :: VL.Lens sub sub sup sup
  super
    = VL.lens upcast (flip smash)
  {-# INLINE super #-}

  -- |Cast the more specific subtype to the more general supertype
  --
  -- >>> upcast human :: Animal
  -- Animal {name = "Tunyasz", age = 50}
  --
  -- >>> upcast (upcast human :: Animal) :: Human
  -- ...
  -- ... The type 'Animal' is not a subtype of 'Human'.
  -- ... The following fields are missing from 'Animal':
  -- ... address
  -- ...
  upcast :: sub -> sup
  upcast = VL.view (super @sup)
  {-# INLINE upcast #-}

  -- |Plug a smaller structure into a larger one
  --
  -- >>> smash (Animal "dog" 10) human
  -- Human {name = "dog", age = 10, address = "London"}
  smash  :: sup -> sub -> sub
  smash = VL.set (super @sup)
  {-# INLINE smash #-}

  {-# MINIMAL super | smash, upcast #-}

instance Core.Context a b => Subtype b a where
    smash p b = to $ Core.gsmash (from p) (from b)
    upcast    = to . Core.gupcast . from

instance {-# OVERLAPPING #-} Subtype a a where
  super = id

-- | See Note [Uncluttering type signatures]
-- >>> :t super
-- super
--   :: (Subtype sup sub, Functor f) => (sup -> f sup) -> sub -> f sub
instance {-# OVERLAPPING #-} Subtype a Void where
  super = undefined

-- | See Note [Uncluttering type signatures]
-- >>> :t super @Int
-- super @Int
--   :: (Subtype Int sub, Functor f) => (Int -> f Int) -> sub -> f sub
instance {-# OVERLAPPING #-} Subtype Void a where
  super = undefined
