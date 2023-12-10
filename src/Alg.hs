{-# LANGUAGE LambdaCase #-}

-- Type algebra.
module Alg (
    Iso(..)
    , Zero(..)
    , One(..)
    , Bifunctor
    , Swap
    , Prod(..)
    , exl
    , exr
    , CoProd(..)
    , destroyCoProd
    , uncoprod
  ) where

import Prelude hiding ((.), id)

-- Iso is a proof that two things are isomorphic.
-- It allows lossly conversion between two types.
data Iso a b = IsoProof { isoAB :: a -> b , isoBA :: b -> a }

-- Iso a b is symmetric.
sym :: Iso a b -> Iso b a
sym (IsoProof ab ba) = IsoProof ba ab

-- Zero is uninhabited
data Zero

-- absurd proves anything from a Zero.
-- ex falso quod libet, when pigs fly, etc..
absurd :: Zero -> a
absurd = \case

-- One has a single element. It carries no data.
data One = One deriving Show

-- Cat is a category.
-- I'm using unusual names here to avoid conflict.
class Cat k where
    id :: a `k` a
    (.) :: (b `k` c) -> (a `k` b) -> (a `k` c)

instance Cat (->) where
    id x = x
    (.) g f x = g (f x)

-- Bifunctor is a functor over a cartesian product of two functors.
-- Here bimap is defined as taking two functions, but
-- it could also be defined as taking a single pair of functions.
class Bifunctor f where
  bimap :: (a -> a') -> (b -> b') -> (f a b -> f a' b')

left :: Bifunctor f => (a -> c) -> f a b -> f c b
left f = bimap f id

right :: Bifunctor f => (b -> c) -> f a b -> f a c
right f = bimap id f

class Swap f where
  swap :: f a b -> f b a

-- swapped bifunctors are isomorphic.
swapIso :: Swap f => Iso (f a b) (f b a)
swapIso = IsoProof { isoAB = swap, isoBA = swap }

-- Prod carries two elements.
-- Prod is associative and its unit is One.
data Prod a b = a :* b deriving Show

-- destroyProd destroys a product of a value and one.
destroyProd :: (Prod a One) -> a
destroyProd (x :* One) = x

instance Bifunctor Prod where
  bimap l r (x :* y) = l x :* r y

-- bimapProd wraps up bimap's function into a single
-- object that is a pair of functions.
bimapProd :: Bifunctor f => Prod (a -> a') (b -> b') -> (f a b -> f a' b')
bimapProd (l :* r) = bimap l r

identProd :: Prod (a -> a) (b -> b)
identProd = id :* id

compProd :: Prod (a' -> a'') (b' -> b'') -> Prod (a -> a') (b -> b') -> Prod (a -> a'') (b -> b'')
compProd (g :* g') (f :* f') = (g . f) :* (g' . f')

exl, exl' :: Prod a b -> a
exl (x :* y) = x
exl' = destroyProd . bimap id (const One)

exr, exr' :: Prod a b -> b
exr (x :* y) = y
exr' = destroyProd . bimap id (const One) . swap

-- One is a unit for products.
prodUnitLeft :: Iso a (Prod One a)
prodUnitLeft = IsoProof{ isoAB = (One :*), isoBA = exr }

prodUnitRight :: Iso a (Prod a One)
prodUnitRight = IsoProof{ isoAB = (:* One), isoBA = exl }

-- Swapped Products are isomorphic.
instance Swap Prod where
  -- swap :: Prod a b -> Prod b a
  swap (x :* y) = (y :* x)

-- products are associative.
prodAssoc :: Iso (Prod (Prod a b) c) (Prod a (Prod b c))
prodAssoc = IsoProof { isoAB = prodRAssoc, isoBA = prodLAssoc }

prodRAssoc :: Prod (Prod a b) c -> Prod a (Prod b c)
prodRAssoc ((x :* y) :* z) = (x :* (y :* z))

prodLAssoc :: Prod a (Prod b c) -> Prod (Prod a b) c
prodLAssoc (x :* (y :* z)) = ((x :* y) :* z)

-- product with zero is zero
prodZeroLeft :: Iso (Prod Zero a) Zero
prodZeroLeft = IsoProof { isoAB = exl, isoBA = absurd }

prodZeroRight :: Iso (Prod a Zero) Zero
prodZeroRight = IsoProof { isoAB = exr, isoBA = absurd }

-- CoProd or sum of a and b, a discriminated union of a and b.
-- CoProd is associative and its unit is Zero.
data CoProd a b = InL a | InR b

-- DestroyCoProd destroys a coprod carrying the same types.
-- It takes a compatible value from either left or right.
destroyCoProd :: CoProd a a -> a
destroyCoProd (InL x) = x
destroyCoProd (InR x) = x

instance Bifunctor CoProd where
  bimap l r (InL x) = InL (l x)
  bimap l r (InR x) = InR (r x)

-- uncoprod destroys any cprod.
uncoprod, uncoprod' :: (a -> c) -> (b -> c) -> CoProd a b -> c
uncoprod l r (InL x) = l x
uncoprod l r (InR x) = r x
uncoprod' l r = destroyCoProd . bimap l r

-- Zero is a unit for CoProd.
coprodUnitLeft :: Iso a (CoProd Zero a)
coprodUnitLeft = IsoProof{ isoAB = InR, isoBA = uncoprod absurd id }

coprodUnitRight :: Iso a (CoProd a Zero)
coprodUnitRight = IsoProof{ isoAB = InL, isoBA = uncoprod id absurd }

-- Swapped CoProducts are isomorphic.
instance Swap CoProd where
  --swap :: CoProd a b -> CoProd b a
  swap = uncoprod InR InL

-- coproducts are associative.
coprodAssoc :: Iso (CoProd (CoProd a b) c) (CoProd a (CoProd b c))
coprodAssoc = IsoProof { isoAB = coprodRAssoc, isoBA = coprodLAssoc }

coprodRAssoc :: CoProd (CoProd a b) c -> CoProd a (CoProd b c)
coprodRAssoc (InL (InL x)) = InL x
coprodRAssoc (InL (InR x)) = InR (InL x)
coprodRAssoc (InR x) = InR (InR x)

coprodLAssoc :: CoProd a (CoProd b c) -> CoProd (CoProd a b) c
coprodLAssoc (InL x) = InL (InL x)
coprodLAssoc (InR (InL x)) = InL (InR x)
coprodLAssoc (InR (InR x)) = InR x

-- Prod distributes over coproducts (sums).
-- a :* (b :+ c) == (a :* b) :+ (a :* c)
distr :: Iso (Prod a (CoProd b c)) (CoProd (Prod a b) (Prod a c))
distr = IsoProof isoAB isoBA
  where isoAB (x :* sum) = uncoprod (InL . (x :*)) (InR . (x :*)) sum
        isoBA = uncoprod (right InL) (right InR)

--
main = do
    print One
    print $ False :* True
