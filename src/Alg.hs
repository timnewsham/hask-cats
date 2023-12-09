
-- Type algebra.
module Alg (
    Iso(..)
    , Zero(..)
    , One(..)
    , Prod(..)
    , CoProd(..)
  ) where

-- Iso is a proof that two things are isomorphic.
-- It allows lossly conversion between two types.
data Iso a b = IsoProof {
    isoAB :: a -> b
    , isoBA :: b -> a
  }

-- Zero is uninhabited
data Zero deriving Show

absurd :: Zero -> a
absurd z = case z of {}

-- One has a single element. It carries no data.
data One = One deriving Show

-- Prod carries two elements.
-- Prod is associative and its unit is One.
data Prod a b = a :* b deriving Show

-- One is a unit for products.
prodUnitLeft :: Iso a (Prod One a)
prodUnitLeft = IsoProof{ isoAB = unitLeft, isoBA = unUnitLeft }
  where unitLeft x = One :* x
        unUnitLeft (One :* x) = x

prodUnitRight :: Iso a (Prod a One)
prodUnitRight = IsoProof{ isoAB = unitRight, isoBA = unUnitRight }
  where unitRight x = x :* One
        unUnitRight (x :* One) = x

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

-- CoProd or sum of a and b, a discriminated union of a and b.
-- CoProd is associative and its unit is Zero.
data CoProd a b = InL a | InR b

-- uncoprod destroys a coprod.
uncoprod :: (a -> c) -> (b -> c) -> CoProd a b -> c
uncoprod l r (InL x) = l x
uncoprod l r (InR x) = r x

-- Zero is a unit for CoProd.
coprodUnitLeft :: Iso a (CoProd Zero a)
coprodUnitLeft = IsoProof{ isoAB = unitLeft, isoBA = unUnitLeft }
  where unitLeft = InR
        unUnitLeft = uncoprod absurd id
        -- unUnitLeft = (InL zero) = absurd zero
        -- unUnitLeft (InR x) = x

coprodUnitRight :: Iso a (CoProd a Zero)
coprodUnitRight = IsoProof{ isoAB = unitRight, isoBA = unUnitRight }
  where unitRight = InL
        unUnitRight = uncoprod id absurd
        -- unUnitRight (InL x) = x
        -- unUnitRight (InR zero) = absurd zero

-- Swapped coproducts are isomorphic.
coswapIso :: Iso (CoProd a b) (CoProd b a)
coswapIso = IsoProof { isoAB = coswap, isoBA = coswap }

coswap :: CoProd a b -> CoProd b a
coswap (InL x) = InR x
coswap (InR x) = InL x

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

--
main = do
    print One
    print $ False :* True


