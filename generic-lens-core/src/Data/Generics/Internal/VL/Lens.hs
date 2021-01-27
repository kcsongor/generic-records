{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Internal.VL.Lens
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Internal lens helpers. Only exported for Haddock
--
-----------------------------------------------------------------------------

module Data.Generics.Internal.VL.Lens
  ( Lens
  , Lens'
  , lens
  , view
  , over
  , set
  , (^.)
  , (%~)
  , (.~)
  , ravel
  , choosing
  , first
  , second
  , lensK1
  , lensM1
  , lensRep
  ) where

import Data.Coerce
import Data.Functor.Const
import Data.Functor.Identity
import GHC.Generics
import Data.Profunctor.Indexed

type LensLike f s t a b = (a -> f b) -> s -> f t

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get set_ = \f x -> set_ x <$> f (get x)
{-# INLINE lens #-}

view :: LensLike (Const a) s s a a -> s -> a
view l s = getConst (l Const s)
{-# INLINE view #-}

over :: LensLike Identity s t a b -> (a -> b) -> s -> t
over = coerce
{-# INLINE over #-}

set :: LensLike Identity s t a b -> b -> s -> t
set l b = over l (\_ -> b)
{-# INLINE set #-}

(^.) :: s -> LensLike (Const a) s s a a -> a
(^.) = flip view
{-# INLINE (^.) #-}
infixl 8 ^.

(%~) :: LensLike Identity s t a b -> (a -> b) -> s -> t
(%~) = over
{-# INLINE (%~) #-}
infixr 4 %~

(.~) :: LensLike Identity s t a b -> b -> s -> t
(.~) = set
{-# INLINE (.~) #-}
infixr 4 .~

-- Normalisation

ravel :: LensLike (Context a b) s t a b -> Lens s t a b
ravel l afb s = case l (Context id) s of
  Context update a -> update <$> afb a
{-# INLINE ravel #-}

-- Utils for core implementation of generic lens

choosing
  :: Lens (s x)  (t x)  a b
  -> Lens (s' x) (t' x) a b
  -> Lens ((s :+: s') x) ((t :+: t') x) a b
choosing l _ f (L1 a)  = L1 <$> l f a
choosing _ r f (R1 a') = R1 <$> r f a'
{-# INLINE choosing #-}

first :: Lens ((a :*: b) x) ((a' :*: b) x) (a x) (a' x)
first f (a :*: b) = (:*: b) <$> f a
{-# INLINE first #-}

second :: Lens ((a :*: b) x) ((a :*: b') x) (b x) (b' x)
second f (a :*: b) = (a :*:) <$> f b
{-# INLINE second #-}

lensK1 :: Lens (K1 r a p) (K1 r b p) a b
lensK1 f (K1 a) = K1 <$> f a
{-# INLINE lensK1 #-}

lensM1 :: Lens (M1 i c f p) (M1 i c g p) (f p) (g p)
lensM1 f (M1 a) = M1 <$> f a
{-# INLINE lensM1 #-}

lensRep :: (Generic a, Generic b) => Lens a b (Rep a x) (Rep b x)
lensRep f a = to <$> f (from a)
{-# INLINE lensRep #-}
