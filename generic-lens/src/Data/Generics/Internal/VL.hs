{-# LANGUAGE PackageImports #-}

module Data.Generics.Internal.VL
  ( module Lens
  , module Iso
  , module Prism
  , module Traversal
  ) where

import "this" Data.Generics.Internal.VL.Iso       as Iso
import "this" Data.Generics.Internal.VL.Prism     as Prism
import "generic-lens-core" Data.Generics.Internal.VL.Lens      as Lens
import "generic-lens-core" Data.Generics.Internal.VL.Traversal as Traversal
