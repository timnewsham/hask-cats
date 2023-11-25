{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Frp ( 
    AddBounds(..)
    , Fun(..)
    , evalFun
    , TimeT(..)
    , FTime
    , TFun
    , Future(..)
    ) where

data AddBounds a = MinBound | NoBound a | MaxBound
  deriving (Eq, Show)

instance Bounded (AddBounds a) where
  minBound = MinBound
  maxBound = MaxBound

instance Ord a => Ord (AddBounds a) where
  MinBound <= _ = True
  _ <= MinBound = False

  (NoBound a) <= (NoBound b) = a < b
  
  _ <= MaxBound = True
  MaxBound <= _ = False

{-
instance Semigroup a => Semigroup (AddBounds a) where
  MinBound <> _ = MinBound
  _ <> MinBound = MinBound

  (NoBound a) <> (NoBound b) = NoBound (a <> b)

  _ <> MaxBound = MaxBound
  MaxBound <> _ = MaxBound

instance Monoid a => Monoid (AddBounds a) where
  mempty = NoBound mempty
  mappend = (<>)
-}

data Fun t a = K a | Fun (t -> a)

newtype TimeT = TimeT Double deriving (Eq, Ord, Show, Num)

type FTime = AddBounds TimeT

-- (<>) on FTime returns the latest time.
instance Semigroup FTime where
  (<>) = max

instance Monoid FTime where
  mempty = minBound

type TFun a = Fun TimeT a

evalFun :: Fun t a -> t -> a
evalFun (K a) _ = a
evalFun (Fun f) t = f t

instance Functor (Fun t) where
  fmap f (K a) = K (f a)
  fmap f (Fun g) = Fun (f . g)

newtype Future a = Fut (FTime, a)
  deriving (Functor, Applicative, Monad, Show)

bottom :: forall t . t
bottom = bottom

-- (<>) on futures returns the soonest one.
instance Semigroup (Future a) where
  (Fut (ta, a)) <> (Fut (tb, b)) = Fut (ta `min` tb, if ta <= tb then a else b)

instance Monoid (Future a) where
  mempty = Fut (maxBound, bottom)
