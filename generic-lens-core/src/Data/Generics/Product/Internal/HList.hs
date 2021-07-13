{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Internal.HList
-- Copyright   :  (C) 2020 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive an isomorphism between a product type and a flat HList.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Internal.HList
  ( GIsList(..)
  , IndexList (..)
  , HList (..)
  , type (++)
  , Elem
  , ListTuple (..)
  , TupleToList
  ) where

import GHC.TypeLits

import Data.Kind    (Type)
import GHC.Generics
import Data.Profunctor.Indexed
import Data.Generics.Internal.Profunctor.Lens
import Data.Generics.Internal.Profunctor.Iso

data HList (as :: [Type]) where
  Nil :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)

infixr 5 :>

type family ((as :: [k]) ++ (bs :: [k])) :: [k] where
  '[]       ++ bs = bs
  (a ': as) ++ bs = a ': as ++ bs

instance Semigroup (HList '[]) where
  _ <> _ = Nil

instance Monoid (HList '[]) where
  mempty  = Nil
  mappend _ _ = Nil

instance (Semigroup a, Semigroup (HList as)) => Semigroup (HList (a ': as)) where
  (x :> xs) <> (y :> ys) = (x <> y) :> (xs <> ys)

instance (Monoid a, Monoid (HList as)) => Monoid (HList (a ': as)) where
  mempty = mempty :> mempty
  mappend (x :> xs) (y :> ys) = mappend x y :> mappend xs ys

class Elem (as :: [(k, Type)]) (key :: k) (i :: Nat) a | as key -> i a
instance {-# OVERLAPPING #-} pos ~ 0 => Elem (a ': xs) key pos a
instance (Elem xs key i a, pos ~ (i + 1)) => Elem (x ': xs) key pos a

class GIsList
  (f :: Type -> Type)
  (g :: Type -> Type)
  (as :: [Type])
  (bs :: [Type]) | f -> as, g -> bs, bs f -> g, as g -> f where

  glist :: Iso (f x) (g x) (HList as) (HList bs)

instance
  ( GIsList l l' as as'
  , GIsList r r' bs bs'
  , Appending as bs cs as' bs' cs'
  , cs ~ (as ++ bs)
  , cs' ~ (as' ++ bs')
  ) => GIsList (l :*: r) (l' :*: r') cs cs' where

  glist = prodIso . pairing glist glist . appending
  {-# INLINE glist #-}

instance GIsList f g as bs => GIsList (M1 t meta f) (M1 t meta g) as bs where
  glist = mIso . glist
  {-# INLINE glist #-}

instance GIsList (Rec0 a) (Rec0 b) '[a] '[b] where
  glist = kIso . singleton
  {-# INLINE glist #-}

instance GIsList U1 U1 '[] '[] where
  glist = iso (const Nil) (const U1)
  {-# INLINE glist #-}

--------------------------------------------------------------------------------
-- | as ++ bs === cs
class Appending as bs cs as' bs' cs'
  | as bs cs cs'   -> as' bs'
  , as' bs' cs cs' -> as bs
  , as bs          -> cs
  , as' bs'        -> cs'
  where
  appending :: Iso (HList as, HList bs) (HList as', HList bs') (HList cs) (HList cs')

-- | [] ++ bs === bs
instance Appending '[] bs bs '[] bs' bs' where
  appending = iso snd (Nil,)

-- | (a : as) ++ bs === (a : cs)
instance
  Appending as bs cs as' bs' cs' -- as ++ bs == cs
  => Appending (a ': as) bs (a ': cs) (a' ': as') bs' (a' ': cs') where
  appending
    = pairing (fromIso consing) id -- ((a, as), bs)
    . assoc3                       -- (a, (as, bs))
    . pairing id appending         -- (a, cs)
    . consing                      -- (a : cs)

singleton :: Iso a b (HList '[a]) (HList '[ b])
singleton = iso (:> Nil) (\(x :> _) -> x)

consing :: Iso (a, HList as) (b, HList bs) (HList (a ': as)) (HList (b ': bs))
consing = iso (\(x, xs) -> x :> xs) (\(x :> xs) -> (x, xs))

--------------------------------------------------------------------------------
class IndexList (i :: Nat) as bs a b | i as -> a, i bs -> b, i as b -> bs, i bs a -> as where
  point :: Lens (HList as) (HList bs) a b

instance {-# OVERLAPPING #-}
  ( as ~ (a ': as')
  , bs ~ (b ': as')
  ) => IndexList 0 as bs a b where
  point = lens (\(x :> xs) -> (xs, x)) (\(xs, x') -> x' :> xs)
  {-# INLINE point #-}

instance
  ( IndexList (n - 1) as' bs' a b
  , as ~ (x ': as')
  , bs ~ (x ': bs')
  ) => IndexList n as bs a b where
  point = fromIso consing . second' . point @(n-1)
  {-# INLINE point #-}

--------------------------------------------------------------------------------
-- * Convert tuples to/from HLists

class ListTuple (tuple :: Type) (tuple' :: Type) (as :: [Type]) (bs :: [Type]) | as -> tuple, bs -> tuple' where
  tupled :: Iso (HList as) (HList bs) tuple tuple'
  tupled = iso (listToTuple @tuple @tuple' @as @bs) (tupleToList @tuple @tuple' @as @bs)
  {-# INLINE tupled #-}

  tupleToList :: tuple' -> HList bs
  listToTuple :: HList as -> tuple

instance ListTuple () () '[] '[]
  where
  tupleToList _ = Nil
  listToTuple _ = ()

instance ListTuple a a' '[a] '[a'] where
  tupleToList a
    = a :> Nil
  listToTuple (a :> Nil)
    = a

instance ListTuple
  (a1, b1) (a2, b2)
  [a1, b1] [a2, b2]
  where
  tupleToList (a, b)
    = a :> b :> Nil
  listToTuple (a :> b :> Nil)
    = (a, b)

instance ListTuple
  (a1, b1, c1) (a2, b2, c2)
  [a1, b1, c1] [a2, b2, c2]
  where
  tupleToList (a, b, c)
    = a :> b :> c :> Nil
  listToTuple (a :> b :> c :> Nil)
    = (a, b, c)

instance ListTuple
  (a1, b1, c1, d1) (a2, b2, c2, d2)
  [a1, b1, c1, d1] [a2, b2, c2, d2]
  where
  tupleToList (a, b, c, d)
    = a :> b :> c :> d:> Nil
  listToTuple (a :> b :> c :> d :> Nil)
    = (a, b, c, d)

instance ListTuple
  (a1, b1, c1, d1, e1) (a2, b2, c2, d2, e2)
  [a1, b1, c1, d1, e1] [a2, b2, c2, d2, e2]
  where
  tupleToList (a, b, c, d, e)
    = a :> b :> c :> d:> e :> Nil
  listToTuple (a :> b :> c :> d :> e :> Nil)
    = (a, b, c, d, e)

instance ListTuple
  (a1, b1, c1, d1, e1, f1) (a2, b2, c2, d2, e2, f2)
  [a1, b1, c1, d1, e1, f1] [a2, b2, c2, d2, e2, f2]
  where
  tupleToList (a, b, c, d, e, f)
    = a :> b :> c :> d:> e :> f :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> Nil)
    = (a, b, c, d, e, f)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1) (a2, b2, c2, d2, e2, f2, g2)
  [a1, b1, c1, d1, e1, f1, g1] [a2, b2, c2, d2, e2, f2, g2]
  where
  tupleToList (a, b, c, d, e, f, g)
    = a :> b :> c :> d:> e :> f :> g :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> Nil)
    = (a, b, c, d, e, f, g)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1) (a2, b2, c2, d2, e2, f2, g2, h2)
  [a1, b1, c1, d1, e1, f1, g1, h1] [a2, b2, c2, d2, e2, f2, g2, h2]
  where
  tupleToList (a, b, c, d, e, f, g, h)
    = a :> b :> c :> d:> e :> f :> g :> h :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> Nil)
    = (a, b, c, d, e, f, g, h)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1) (a2, b2, c2, d2, e2, f2, g2, h2, j2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1] [a2, b2, c2, d2, e2, f2, g2, h2, j2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> Nil)
    = (a, b, c, d, e, f, g, h, j)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> Nil)
    = (a, b, c, d, e, f, g, h, j, k)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n, o)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1, r1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2, r2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1, r1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2, r2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> r :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> r :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r)

instance ListTuple
  (a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1) (a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2, r2, s2)
  [a1, b1, c1, d1, e1, f1, g1, h1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1] [a2, b2, c2, d2, e2, f2, g2, h2, j2, k2, l2, m2, n2, o2, p2, q2, r2, s2]
  where
  tupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r, s)
    = a :> b :> c :> d:> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> Nil
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> Nil)
    = (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r, s)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v)
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v]
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46', a47')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46', a47']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> a47 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> a47 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47)

instance ListTuple
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48) (a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46', a47', a48')
  [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48] [a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p', q', r', s', t', u', v', w', x', y', z', a26', a27', a28', a29', a30', a31', a32', a33', a34', a35', a36', a37', a38', a39', a40', a41', a42', a43', a44', a45', a46', a47', a48']
  where
  tupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48)
    = (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> a47 :> a48 :> Nil)
  listToTuple (a :> b :> c :> d :> e :> f :> g :> h :> i :> j :> k :> l :> m :> n :> o :> p :> q :> r :> s :> t :> u :> v :> w :> x :> y :> z :> a26 :> a27 :> a28 :> a29 :> a30 :> a31 :> a32 :> a33 :> a34 :> a35 :> a36 :> a37 :> a38 :> a39 :> a40 :> a41 :> a42 :> a43 :> a44 :> a45 :> a46 :> a47 :> a48 :> Nil)
    = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48)

type family TupleToList a where
  TupleToList () = '[]
  TupleToList (a, b) = '[a, b]
  TupleToList (a, b, c) = '[a, b, c]
  TupleToList (a, b, c, d) = '[a, b, c, d]
  TupleToList (a, b, c, d, e) = '[a, b, c, d, e]
  TupleToList (a, b, c, d, e, f) = '[a, b, c, d, e, f]
  TupleToList (a, b, c, d, e, f, g) = '[a, b, c, d, e, f, g]
  TupleToList (a, b, c, d, e, f, g, h) = '[a, b, c, d, e, f, g, h]
  TupleToList (a, b, c, d, e, f, g, h, j) = '[a, b, c, d, e, f, g, h, j]
  TupleToList (a, b, c, d, e, f, g, h, j, k) = '[a, b, c, d, e, f, g, h, j, k]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l) = '[a, b, c, d, e, f, g, h, j, k, l]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m) = '[a, b, c, d, e, f, g, h, j, k, l, m]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n) = '[a, b, c, d, e, f, g, h, j, k, l, m, n]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o) = '[a, b, c, d, e, f, g, h, j, k, l, m, n, o]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p) = '[a, b, c, d, e, f, g, h, j, k, l, m, n, o, p]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q) = '[a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r) = '[a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r]
  TupleToList (a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r, s) = '[a, b, c, d, e, f, g, h, j, k, l, m, n, o, p, q, r, s]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47]
  TupleToList (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48) = '[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48]
  TupleToList a = '[a]
