{-# LANGUAGE EmptyCase #-}

-- Type algebra.
module Alg (
    Iso(..)
    , Zero(..)
    , One(..)
    , Prod(..)
    , exl
    , exr
    , prodMap
    , swap
    , CoProd(..)
    , uncoprod
    , coswap
  ) where

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
absurd z = case z of {}

-- One has a single element. It carries no data.
data One = One deriving Show

-- Prod carries two elements.
-- Prod is associative and its unit is One.
data Prod a b = a :* b deriving Show

exl :: Prod a b -> a
exl (x :* y) = x

exr :: Prod a b -> b
exr (x :* y) = y

prodMap :: (a -> c) -> (b -> d) -> Prod a b -> Prod c d
prodMap l r (x :* y) = l x :* r y

left :: (a -> c) -> Prod a b -> Prod c b
left f = prodMap f id

right :: (b -> c) -> Prod a b -> Prod a c
right f = prodMap id f

-- One is a unit for products.
prodUnitLeft :: Iso a (Prod One a)
prodUnitLeft = IsoProof{ isoAB = (One :*), isoBA = exr }

prodUnitRight :: Iso a (Prod a One)
prodUnitRight = IsoProof{ isoAB = (:* One), isoBA = exl }

-- swapped products are isomorphic.
swapIso :: Iso (Prod a b) (Prod b a)
swapIso = IsoProof { isoAB = swap, isoBA = swap }

swap :: Prod a b -> Prod b a
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

-- uncoprod destroys a coprod.
uncoprod :: (a -> c) -> (b -> c) -> CoProd a b -> c
uncoprod l r (InL x) = l x
uncoprod l r (InR x) = r x

-- Zero is a unit for CoProd.
coprodUnitLeft :: Iso a (CoProd Zero a)
coprodUnitLeft = IsoProof{ isoAB = InR, isoBA = uncoprod absurd id }

coprodUnitRight :: Iso a (CoProd a Zero)
coprodUnitRight = IsoProof{ isoAB = InL, isoBA = uncoprod id absurd }

-- Swapped coproducts are isomorphic.
coswapIso :: Iso (CoProd a b) (CoProd b a)
coswapIso = IsoProof { isoAB = coswap, isoBA = coswap }

coswap :: CoProd a b -> CoProd b a
coswap = uncoprod InR InL

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
