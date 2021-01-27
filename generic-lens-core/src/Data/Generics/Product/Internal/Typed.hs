{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Generics.Product.Internal.Typed
 ( Context
 , derived
 ) where

import Data.Generics.Internal.Families
import Data.Generics.Product.Internal.GLens

import Data.Kind    (Constraint, Type)
import GHC.Generics (Generic (Rep))
import GHC.TypeLits (TypeError, ErrorMessage (..))
import Data.Generics.Internal.VL.Lens
import Data.Generics.Internal.Errors

type Context a s = ( Generic s
  , ErrorUnlessOne a s (CollectTotalType a (Rep s))
  , Defined (Rep s)
    (NoGeneric s '[ 'Text "arising from a generic lens focusing on a field of type " ':<>: QuoteType a])
    (() :: Constraint)
  , GLens (HasTotalTypePSym a) (Rep s) (Rep s) a a
  )

derived :: forall a s. Context a s => Lens s s a a
derived = lensRep . glens @(HasTotalTypePSym a)
{-# INLINE derived #-}

type family ErrorUnlessOne (a :: Type) (s :: Type) (stat :: TypeStat) :: Constraint where
  ErrorUnlessOne a s ('TypeStat '[_] '[] '[])
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " does not contain a value of type "
        ':<>: 'ShowType a
        )

  ErrorUnlessOne a s ('TypeStat (n ': ns) _ _)
    = TypeError
        (     'Text "Not all constructors of the type "
        ':<>: 'ShowType s
        ':<>: 'Text " contain a field of type "
        ':<>: 'ShowType a ':<>: 'Text "."
        ':$$: 'Text "The offending constructors are:"
        ':$$: ShowSymbols (n ': ns)
        )

  ErrorUnlessOne a s ('TypeStat _ (m ': ms) _)
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " contains multiple values of type "
        ':<>: 'ShowType a ':<>: 'Text "."
        ':$$: 'Text "The choice of value is thus ambiguous. The offending constructors are:"
        ':$$: ShowSymbols (m ': ms)
        )

  ErrorUnlessOne _ _ ('TypeStat '[] '[] _)
    = ()

data HasTotalTypePSym :: Type -> (TyFun (Type -> Type) (Maybe Type))
type instance Eval (HasTotalTypePSym t) tt = HasTotalTypeP t tt
