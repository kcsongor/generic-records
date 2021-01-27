{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE Rank2Types #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Internal.Profunctor.Lens
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Internal lens helpers. Only exported for Haddock
--
-----------------------------------------------------------------------------
module Data.Generics.Internal.Profunctor.Lens where

import Data.Profunctor.Indexed (Profunctor(..), Strong(..))

type Lens s t a b
  = forall p i . Strong p => p i a b -> p i s t

lens :: (s -> (c, a)) -> ((c, b) -> t) -> Lens s t a b
lens get set = dimap get set . second'
{-# INLINE lens #-}
