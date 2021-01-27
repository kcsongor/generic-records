{-# LANGUAGE TypeInType #-}
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
-- Module      :  Data.Generics.Product.Internal.Positions
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive positional product type getters and setters generically.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Internal.Positions
  ( type (<?)
  , Size
  , CRep

  , Context
  , Context_
  , Context'
  , Context0
  , derived0
  , derived'
  ) where

import Data.Kind      (Type, Constraint)
import Data.Type.Bool (If, Not, type (&&))
import GHC.Generics
import GHC.TypeLits   (type (<=?), type (+), Nat, TypeError, ErrorMessage(..))
import Data.Coerce
  
import Data.Generics.Internal.Families
import Data.Generics.Product.Internal.GLens
import Data.Generics.Internal.Errors
import Data.Generics.Internal.VL.Lens

type Context' (i :: Nat) s a
  = ( Generic s
    , ErrorUnless i s (0 <? i && i <=? Size (Rep s))
    , Coercible (Rep s) (CRep s)
    , GLens' (HasTotalPositionPSym i) (CRep s) a
    , Defined (Rep s)
      (NoGeneric s '[ 'Text "arising from a generic lens focusing on the field at"
                    , 'Text "position " ':<>: QuoteType i ':<>: 'Text " of type " ':<>: QuoteType a
                      ':<>: 'Text " in " ':<>: QuoteType s
                    ])
      (() :: Constraint)
    )

class Context (i :: Nat) s t a b | s i -> a, t i -> b, s i b -> t, t i a -> s
instance
  ( ErrorUnless i s (0 <? i && i <=? Size (Rep s))
  , HasTotalPositionP i (CRep s) ~ 'Just a
  , HasTotalPositionP i (CRep t) ~ 'Just b
  , HasTotalPositionP i (CRep (Indexed s)) ~ 'Just a'
  , HasTotalPositionP i (CRep (Indexed t)) ~ 'Just b'
  , t ~ Infer s a' b
  , s ~ Infer t b' a
  ) => Context i s t a b

type Context_ i s t a b = 
  ( ErrorUnless i s (0 <? i && i <=? Size (Rep s))
  , UnifyHead s t
  , UnifyHead t s
  )

type Context0 i s t a b
  = ( Generic s
    , Generic t
    , GLens (HasTotalPositionPSym i) (CRep s) (CRep t) a b
    , Coercible (CRep s) (Rep s)
    , Coercible (CRep t) (Rep t)
    , Defined (Rep s)
      (NoGeneric s '[ 'Text "arising from a generic lens focusing on the field at"
                    , 'Text "position " ':<>: QuoteType i ':<>: 'Text " of type " ':<>: QuoteType a
                      ':<>: 'Text " in " ':<>: QuoteType s
                    ])
      (() :: Constraint)
    )

derived0 :: forall i s t a b. Context0 i s t a b => Lens s t a b
derived0 = (lensRep . coerced @(CRep s) @(CRep t) . glens @(HasTotalPositionPSym i))
{-# INLINE derived0 #-}

derived' :: forall i s a. Context' i s a => Lens s s a a
derived' = (lensRep . coerced @(CRep s) @(CRep s) . glens @(HasTotalPositionPSym i))
{-# INLINE derived' #-}

type family ErrorUnless (i :: Nat) (s :: Type) (hasP :: Bool) :: Constraint where
  ErrorUnless i s 'False
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " does not contain a field at position "
        ':<>: 'ShowType i
        )

  ErrorUnless _ _ 'True
    = ()

data HasTotalPositionPSym  :: Nat -> (TyFun (Type -> Type) (Maybe Type))
type instance Eval (HasTotalPositionPSym t) tt = HasTotalPositionP t tt

  
-- We wouldn't need the universal 'x' here if we could express above that
-- forall x. Coercible (cs x) (Rep s x), but this requires quantified
-- constraints
coerced :: forall s t s' t' x. (Coercible t t', Coercible s s')
        => Lens (s' x) (t' x) (s x) (t x)
coerced f s = coerce <$> f (coerce s)
{-# INLINE coerced #-}

--------------------------------------------------------------------------------  

-- | Alias for the kind of the generic rep
type G = Type -> Type

--------------------------------------------------------------------------------

-- | In-order labeling of the generic tree with the field positions
--
-- We replace the (K1 R a) nodes with (K1 (Pos n) a), where 'n' is the position
-- of the field in question in the data type. This is convenient, because we
-- can reuse all the existing functions as long as they are polymorphic in the
-- first parameter of 'K1'.
type family CRep (a :: Type) :: G where
  CRep rep = Fst (Traverse (Rep rep) 1)

-- | The actual traversal.
--
-- Might be cleaner if the sum and product parts were separated (as there's
-- and invariant that 'n' should be zero when we're at a sum node, which holds
-- for derived Generic instances (where the sums are strictly above the products))
type family Traverse (a :: G) (n :: Nat) :: (G, Nat) where
  Traverse (M1 mt m s) n
    = Traverse1 (M1 mt m) (Traverse s n)
  Traverse (l :+: r) n
    = '(Fst (Traverse l n) :+: Fst (Traverse r n), n)
  Traverse (l :*: r) n
    = TraverseProd (:*:) (Traverse l n) r
  Traverse (K1 _ p) n
    = '(K1 (Pos n) p, n + 1)
  Traverse U1 n
    = '(U1, n)

type family Traverse1 (w :: G -> G) (z :: (G, Nat)) :: (G, Nat) where
  Traverse1 w '(i, n) = '(w i, n)

-- | For products, we first traverse the left-hand side, followed by the second
-- using the counter returned by the left traversal.
type family TraverseProd (c :: G -> G -> G) (a :: (G, Nat)) (r :: G) :: (G, Nat) where
  TraverseProd w '(i, n) r = Traverse1 (w i) (Traverse r n)

--------------------------------------------------------------------------------
-- Utilities

type family Fst (p :: (a, b)) :: a where
  Fst '(a, b) = a

type family Size f :: Nat where
  Size (l :*: r)
    = Size l + Size r
  Size (l :+: r)
    = Min (Size l) (Size r)
  Size (D1 meta f)
    = Size f
  Size (C1 meta f)
    = Size f
  Size f
    = 1

type x <? y = Not (y <=? x)
infixl 4 <?

type Min a b = If (a <? b) a b
