{-# OPTIONS_HADDOCK hide          #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      : Data.Generics.Internal.GenericN
-- Copyright   : (C) 2020 Csongor Kiss
-- License     : BSD3
-- Maintainer  : Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- Generic representation of types with multiple parameters
--
--------------------------------------------------------------------------------

module Data.Generics.Internal.GenericN
  ( Param (..)
  , Rec (Rec, unRec)
  , GenericN (..)
  ) where

import Data.Kind
import GHC.Generics
import GHC.TypeLits
import Data.Coerce

data family Param :: Nat -> j -> Type

newtype instance Param n (a :: Type)
  = StarParam { getStarParam :: a}

type family Indexed (t :: k) (i :: Nat) :: k where
  Indexed (t a) i = Indexed t (i + 1) (Param i a)
  Indexed t _     = t

newtype Rec (p :: Type) a x = Rec { unRec :: K1 R a x }

class
  ( Coercible (Rep a) (RepN a)
  , Generic a
  ) => GenericN (a :: Type) where
  type family RepN (a :: Type) :: Type -> Type
  type instance RepN a = Rep (Indexed a 0)
  toN :: RepN a x -> a
  fromN :: a -> RepN a x

instance
  ( Coercible (Rep a) (RepN a)
  , Generic a
  ) => GenericN a where
  toN :: forall x. RepN a x -> a
  toN   = coerce (to :: Rep a x -> a)
  {-# INLINE toN #-}

  fromN :: forall x. a -> RepN a x
  fromN = coerce (from :: a -> Rep a x)
  {-# INLINE fromN #-}
