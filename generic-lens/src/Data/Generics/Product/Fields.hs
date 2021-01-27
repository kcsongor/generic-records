{-# LANGUAGE PackageImports #-}
{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Fields
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive record field getters and setters generically.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Fields
  ( -- *Lenses

    -- $setup
    HasField (..)
  , HasField' (..)
  , HasField_ (..)

  , getField
  , setField
  ) where

import "generic-lens-core" Data.Generics.Internal.Void
import qualified "generic-lens-core" Data.Generics.Internal.VL.Lens as VL
import qualified "generic-lens-core" Data.Generics.Product.Internal.Fields as Core

import GHC.TypeLits (Symbol)

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
-- data Human a
--   = Human
--     { name    :: String
--     , age     :: Int
--     , address :: String
--     , other   :: a
--     }
--   | HumanNoAddress
--     { name    :: String
--     , age     :: Int
--     , other   :: a
--     }
--   deriving (Generic, Show)
-- human :: Human Bool
-- human = Human { name = "Tunyasz", age = 50, address = "London", other = False }
-- :}

-- |Records that have a field with a given name.
class HasField (field :: Symbol) s t a b | s field -> a, t field -> b, s field b -> t, t field a -> s where
  -- |A lens that focuses on a field with a given name. Compatible with the
  --  lens package's 'Control.Lens.Lens' type.
  --
  --  >>> human ^. field @"age"
  --  50
  --
  --  === /Type changing/
  --
  --  >>> :t human
  --  human :: Human Bool
  --
  --  >>> :t human & field @"other" .~ (42 :: Int)
  --  human & field @"other" .~ (42 :: Int) :: Human Int
  --
  --  >>> human & field @"other" .~ 42
  --  Human {name = "Tunyasz", age = 50, address = "London", other = 42}
  --
  --  === /Type errors/
  --
  --  >>> human & field @"weight" .~ 42
  --  ...
  --  ... The type Human Bool does not contain a field named 'weight'.
  --  ...
  --
  --  >>> human & field @"address" .~ ""
  --  ...
  --  ... Not all constructors of the type Human Bool
  --  ... contain a field named 'address'.
  --  ... The offending constructors are:
  --  ... HumanNoAddress
  --  ...
  field :: VL.Lens s t a b

-- |Records that have a field with a given name.
--
-- This is meant to be more general than 'HasField', but that is not quite the
-- case due to the lack of functional dependencies.
--
-- The types @s@ and @t@ must be applications of the same type constructor.
-- In contrast, 'HasField' also requires the parameters of that type constructor
-- to have representational roles.
--
-- One use case of 'HasField_' over 'HasField' is for records defined with
-- @data instance@.
class HasField_ (field :: Symbol) s t a b where
  field_ :: VL.Lens s t a b

class HasField' (field :: Symbol) s a | s field -> a where
  field' :: VL.Lens s s a a

-- |Records that have a field with a given name.
--
-- This class gives the minimal constraints needed to define this lens.
-- For common uses, see 'HasField'.
class HasField0 (field :: Symbol) s t a b where
  field0 :: VL.Lens s t a b

-- |
-- >>> getField @"age" human
-- 50
getField :: forall f a s.  HasField' f s a => s -> a
getField = VL.view (field' @f)

-- |
-- >>> setField @"age" 60 human
-- Human {name = "Tunyasz", age = 60, address = "London", other = False}
setField :: forall f s a. HasField' f s a => a -> s -> s
setField = VL.set (field' @f)

instance Core.Context' field s a => HasField' field s a where
  field' f s = field0 @field f s

instance (Core.Context field s t a b , HasField0 field s t a b) => HasField field s t a b where
  field f s = field0 @field f s

-- instance {-# OVERLAPPING #-} HasField' field s a => HasField field s s a a where
--   field f s = field' @field f s

-- | See Note [Uncluttering type signatures]
-- >>> :t field
-- field
--   :: (HasField field s t a b, Functor f) => (a -> f b) -> s -> f t
instance {-# OVERLAPPING #-} HasField f (Void1 a) (Void1 b) a b where
  field = undefined

instance {-# OVERLAPPING #-} HasField' f (Void1 a) a where
  field' = undefined

instance (Core.Context_ field s t a b , HasField0 field s t a b) => HasField_ field s t a b where
  field_ f s = field0 @field f s

instance {-# OVERLAPPING #-} HasField_ f (Void1 a) (Void1 b) a b where
  field_ = undefined

instance Core.Context0 field s t a b => HasField0 field s t a b where
  field0 = VL.ravel (Core.derived @field)
  {-# INLINE field0 #-}
