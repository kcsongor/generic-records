{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Internal.Profunctor.Iso
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Internal lens helpers. Only exported for Haddock
--
-----------------------------------------------------------------------------
module Data.Generics.Internal.Profunctor.Iso where

import Data.Profunctor.Indexed
import GHC.Generics           ((:*:)(..), (:+:)(..), Generic(..), M1(..), K1(..), Rep)
import Data.Generics.Internal.GenericN (Rec (..))

-- import qualified Data.Generics.Internal.VL.Iso as VL

type Iso s t a b
  = forall p i. (Profunctor p) => p i a b -> p i s t

type Iso' s a = Iso s s a a

-- | A type and its generic representation are isomorphic
repIso :: (Generic a, Generic b) => Iso a b (Rep a x) (Rep b x)
repIso = iso from to
{-# INLINE repIso #-}

-- | 'M1' is just a wrapper around `f p`
--mIso :: Iso' (M1 i c f p) (f p)
mIso :: Iso (M1 i c f p) (M1 i c g p) (f p) (g p)
mIso = iso unM1 M1
{-# INLINE mIso #-}

kIso :: Iso (K1 r a p) (K1 r b p) a b
kIso = iso unK1 K1
{-# INLINE kIso #-}

recIso :: Iso (Rec r a p) (Rec r b p) a b
recIso = iso (unK1 . unRec) (Rec . K1)
{-# INLINE recIso #-}

sumIso :: Iso ((a :+: b) x) ((a' :+: b') x) (Either (a x) (b x)) (Either (a' x) (b' x))
sumIso = iso back forth
  where forth (Left l)  = L1 l
        forth (Right r) = R1 r
        back (L1 l) = Left l
        back (R1 r) = Right r
{-# INLINE sumIso #-}

prodIso :: Iso ((a :*: b) x) ((a' :*: b') x) (a x, b x) (a' x, b' x)
prodIso = iso (\(a :*: b) -> (a, b)) (\(a, b) -> (a :*: b))
{-# INLINE prodIso #-}

assoc3 :: Iso ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
assoc3 = iso (\((a, b), c) -> (a, (b, c))) (\(a, (b, c)) -> ((a, b), c))
{-# INLINE assoc3 #-}

--------------------------------------------------------------------------------
-- Iso stuff

fromIso :: Iso s t a b -> Iso b a t s
fromIso l = withIso l $ \ sa bt -> iso bt sa
{-# INLINE fromIso #-}

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso sa bt = dimap sa bt
{-# INLINE iso #-}

withIso :: Iso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k = case ai (Exchange id id) of
  Exchange sa bt -> k sa bt
{-# INLINE withIso #-}

pairing :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
pairing f g = withIso f $ \sa bt -> withIso g $ \s'a' b't' ->
  iso (bimap sa s'a') (bimap bt b't')
  where
    -- Data.Bifunctor.bimap is too lazy
    bimap f' g' (a, b) = (f' a, g' b)
{-# INLINE pairing #-}

isoFirst :: Iso s t a b -> Iso (s, x) (t, y) (a, x) (b, y)
isoFirst o = withIso o $ \sa bt -> iso (first sa) (first bt)
  where
    -- Data.Bifunctor.first is too lazy
    first f (a, b) = (f a, b)
{-# INLINE isoFirst #-}

isoSecond :: Iso s t a b -> Iso (x, s) (y, t) (x, a) (y, b)
isoSecond o = withIso o $ \sa bt -> iso (second sa) (second bt)
  where
    -- Data.Bifunctor.second is too lazy
    second f (a, b) = (a, f b)
{-# INLINE isoSecond #-}
