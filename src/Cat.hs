{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Cat (
  AssociativeCat (rassoc, lassoc)
  , BraidedCat (swap)
  , Terminal (it)
  , ConstCat (unitArrow)
  , constC
  , MonoidalS (sum)
  , join 
  , CoCartesian (inl, inr, jam)
  , MonoidalP (first, second, cross)
  , fork
  , Cartesian (exl, exr, dup)
  , Distributive (distl, distr, undistl, undistr)
  , BoolCat (notC, andC, orC)
  , NumCat (negateC, addC, subC, mulC)
  ) where

import Prelude hiding ((.), id, sum)
import Control.Category

class AssociativeCat k where
  rassoc :: ((a, b), c) `k` (a, (b, c))
  lassoc :: (a, (b, c)) `k` ((a, b), c)

instance AssociativeCat (->) where
  rassoc ((a, b), c) = (a, (b, c))
  lassoc (a, (b, c)) = ((a, b), c)

class BraidedCat k where
  swap :: (a, b) `k` (b, a)

instance BraidedCat (->) where
  swap (a, b) = (b, a)

class Cartesian k where
  exl :: (a, b) `k` a
  exr :: (a, b) `k` b
  dup :: a `k` (a, a)

instance Cartesian (->) where
  exl (a, _) = a
  exr (_, b) = b
  dup a = (a, a)

class Category k => MonoidalP k where
  cross :: (a `k` c) -> (b `k` d) -> ((a, b) `k` (c, d))
  f `cross` g = first f . second g

  first :: (a `k` c) -> ((a, b) `k` (c, b))
  first f = f `cross` id

  second :: (b `k` d) -> ((a, b) `k` (a, d))
  second g = id `cross` g

fork :: (Cartesian k, MonoidalP k) => (a `k` c) -> (a `k` d) -> (a `k` (c, d))
fork f g = (f `cross` g) . dup

instance MonoidalP (->) where
  cross f g (a, b) = (f a, g b)
  -- first f (a, b) = (f a, b)
  -- second g (a, b) = (a, g b)

class Category k => MonoidalS k where
  sum :: (a `k` c) -> (b `k` d) -> (Either a b `k` Either c d)

instance MonoidalS (->) where
  sum f _ (Left x) = Left $ f x
  sum _ g (Right y) = Right $ g y

class CoCartesian k where
  inl :: a `k` (Either a b)
  inr :: b `k` (Either a b)
  jam :: (Either a a) `k` a

instance CoCartesian (->) where
  inl = Left
  inr = Right
  jam = either id id

join :: (CoCartesian k, MonoidalS k) => (a `k` c) -> (b `k` c) -> (Either a b `k` c)
join f g = jam . (f `sum` g)

class (Cartesian k, CoCartesian k) => Distributive k where
  distl :: (a, Either u v) `k` (Either (a, u) (a, v))
  distr :: (Either u v, b) `k` (Either (u, b) (v, b))
  undistl :: (Either (a, u) (a, v)) `k` (a, Either u v)
  undistr :: (Either (u, b) (v, b)) `k` (Either u v, b)

instance Distributive (->) where
  distl (a, Left b) = Left (a, b)
  distl (a, Right b) = Right (a, b)

  distr (Left a, b) = Left (a, b)
  distr (Right a, b) = Right (a, b)

  -- undistl (Left (a,b)) = (a, Left b)
  -- undistl (Right (a,b)) = (a, Right b)
  undistl = second inl `join` second inr

  -- undistr (Left (a,b)) = (Left a, b)
  -- undistr (Right (a,b)) = (Right a, b)
  undistr = first inl `join` first inr



class Category k => Terminal k where
  it :: a `k` ()

instance Terminal (->) where
  it = const ()

class ConstCat k b where
  unitArrow :: b -> (() `k` b)
  --constC :: b -> (a `k` b)

instance ConstCat (->) b where
  unitArrow b = \() -> b
  --constC = const

constC :: (Terminal k, ConstCat k b) => b -> (a `k` b)
constC b = unitArrow b . it

class Cartesian k => BoolCat k where
  notC :: Bool `k` Bool
  andC, orC :: (Bool, Bool) `k` Bool

instance BoolCat (->) where
  notC = not
  andC = uncurry (&&)
  orC = uncurry (||)

class Cartesian k => NumCat k a where
  negateC :: a `k` a
  addC, subC, mulC :: (a, a) `k` a

instance Num a => NumCat (->) a where
  negateC = negate
  addC = uncurry (+)
  subC = uncurry (-)
  mulC = uncurry (*)
