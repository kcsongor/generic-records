{-# LANGUAGE FlexibleContexts #-}
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

module Data.Generics.Product.Internal.Fields
  ( Context_
  , Context'
  , Context0
  , Context
  , derived
  ) where

import Data.Generics.Internal.Families
import Data.Generics.Product.Internal.GLens
import Data.Kind    (Constraint, Type)
import GHC.Generics
import GHC.TypeLits (Symbol, ErrorMessage(..), TypeError)
import Data.Generics.Internal.Errors
import Data.Generics.Internal.VL.Lens

-- Full context
class Context (field :: Symbol) s t a b | s field -> a, t field -> b, s field b -> t, t field a -> s
instance
  ( HasTotalFieldP field (Rep s) ~ 'Just a
  , HasTotalFieldP field (Rep t) ~ 'Just b
  , HasTotalFieldP field (Rep (Indexed s)) ~ 'Just a'
  , HasTotalFieldP field (Rep (Indexed t)) ~ 'Just b'
  , t ~ Infer s a' b
  , s ~ Infer t b' a
  ) => Context field s t a b

-- Alternative type inference
type Context_ field s t a b
  = ( HasTotalFieldP field (Rep s) ~ 'Just a
    , HasTotalFieldP field (Rep t) ~ 'Just b
    , UnifyHead s t
    , UnifyHead t s
    )

-- Monomorphic
type Context' field s a
  = ( Generic s
    , ErrorUnless field s (CollectField field (Rep s))
    , GLens' (HasTotalFieldPSym field) (Rep s) a
    , Defined (Rep s)
      (NoGeneric s '[ 'Text "arising from a generic lens focusing on the "
                      ':<>: QuoteType field ':<>: 'Text " field of type " ':<>: QuoteType a
                    , 'Text "in " ':<>: QuoteType s])
      (() :: Constraint)
    )

-- No inference
type Context0 field s t a b
  = ( Generic s
    , Generic t
    , GLens  (HasTotalFieldPSym field) (Rep s) (Rep t) a b
    , ErrorUnless field s (CollectField field (Rep s))
    , Defined (Rep s)
      (NoGeneric s '[ 'Text "arising from a generic lens focusing on the "
                      ':<>: QuoteType field ':<>: 'Text " field of type " ':<>: QuoteType a
                    , 'Text "in " ':<>: QuoteType s])
      (() :: Constraint)
    )

derived :: forall field s t a b. Context0 field s t a b => Lens s t a b
derived = lensRep . glens @(HasTotalFieldPSym field)
{-# INLINE derived #-}

type family ErrorUnless (field :: Symbol) (s :: Type) (stat :: TypeStat) :: Constraint where
  ErrorUnless field s ('TypeStat _ _ '[])
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " does not contain a field named '"
        ':<>: 'Text field ':<>: 'Text "'."
        )

  ErrorUnless field s ('TypeStat (n ': ns) _ _)
    = TypeError
        (     'Text "Not all constructors of the type "
        ':<>: 'ShowType s
        ':$$: 'Text " contain a field named '"
        ':<>: 'Text field ':<>: 'Text "'."
        ':$$: 'Text "The offending constructors are:"
        ':$$: ShowSymbols (n ': ns)
        )

  ErrorUnless _ _ ('TypeStat '[] '[] _)
    = ()

data HasTotalFieldPSym :: Symbol -> (TyFun (Type -> Type) (Maybe Type))
type instance Eval (HasTotalFieldPSym sym) tt = HasTotalFieldP sym tt
