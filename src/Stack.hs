{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Stack ( 
    unSF
    , unSP
    , progFun
    , ops_
    , evalStackOps0
    , evalStackProg0
    , StackProg
    ) where

import Prelude hiding ((.), id, sum)
import Data.Kind
import Data.List (intercalate)
import Control.Category
import Cat

newtype StackFun a b = SF { unSF :: forall z . (a, z) -> (b, z) }

stackFun :: (a -> b) -> StackFun a b
stackFun f = SF (first f)

instance Category StackFun where
  id = SF id
  SF g . SF f = SF (g . f)

instance AssociativeCat StackFun where
  rassoc = stackFun rassoc
  lassoc = stackFun lassoc

instance BraidedCat StackFun where
  swap = stackFun swap

instance MonoidalP StackFun where
  first (SF f) = SF (lassoc . f . rassoc)
  second g = swap . first g . swap
  f `cross` g = first f . second g

instance Cartesian StackFun where
  exl = stackFun exl
  exr = stackFun exr
  dup = stackFun dup

instance MonoidalS StackFun where
  (SF f) `sum` (SF g) = SF (undistr . (f `sum` g) . distr)

instance CoCartesian StackFun where
  inl = stackFun inl
  inr = stackFun inr
  jam = stackFun jam

data Prim :: Type -> Type -> Type where
  Exl :: Prim (a, b) a
  Exr :: Prim (a, b) b
  Dup :: Prim a (a, a)
  Swap :: Prim (a, b) (b, a)
  Negate :: Num a => Prim a a
  Add, Sub, Mul :: Num a => Prim (a, a) a
  Const :: Show a => a -> Prim b a

instance Show (Prim a b) where
  show Exl = "Exl"
  show Exr = "Exr"
  show Dup = "Dup"
  show Swap = "Swap"
  show Negate = "Negate"
  show Add = "Add"
  show Sub = "Sub"
  show Mul = "Mul"
  show (Const a) = "Const " ++ show a

evalPrim :: Prim a b -> (a -> b)
evalPrim Exl = exl
evalPrim Exr = exr
evalPrim Dup = dup
evalPrim Negate = negateC
evalPrim Add = addC
evalPrim Sub = subC
evalPrim Mul = mulC
evalPrim Swap = swap
evalPrim (Const a) = constC a

data StackOp :: Type -> Type -> Type where
  Prim :: Prim a b -> StackOp (a, z) (b, z)
  Push :: StackOp ((a, b), z) (a, (b, z))
  Pop :: StackOp (a, (b, z)) ((a, b), z)

instance Show (StackOp a b) where
  show Push = "Push"
  show Pop = "Pop"
  show (Prim p) = show p

evalStackOp :: StackOp u v -> (u -> v)
evalStackOp (Prim f) = first (evalPrim f)
evalStackOp Push = rassoc
evalStackOp Pop = lassoc

infixr 5 :<
data StackOps :: Type -> Type -> Type where
  Nil :: StackOps a a
  (:<) :: StackOp a b -> StackOps b c -> StackOps a c

mapStackOpsToList :: (forall c d . StackOp c d -> e) -> StackOps a b -> [e]
mapStackOpsToList _ Nil = []
mapStackOpsToList f (op :< ops) = f op : mapStackOpsToList f ops

instance Show (StackOps a b) where
  show = intercalate ", " . mapStackOpsToList show

opsconcat :: StackOps a b -> StackOps b c -> StackOps a c
opsconcat Nil ops = ops
opsconcat (op :< ops1) ops2 = op :< (ops1 `opsconcat` ops2)

evalStackOps :: StackOps u v -> (u -> v)
evalStackOps Nil = id
evalStackOps (op :< ops) = evalStackOps ops . evalStackOp op

data StackProg a b = SP { unSP :: forall z . StackOps (a, z) (b, z) }

instance Show (StackProg a b) where
  show (SP ops) = show ops

instance Category StackProg where
  id = SP Nil
  SP g . SP f = SP (f `opsconcat` g)

instance BraidedCat StackProg where
  swap = primProg Swap

instance MonoidalP StackProg where
  first (SP ops) = SP (Push :< ops `opsconcat` (Pop :< Nil))
  second g = swap . first g . swap
  f `cross` g = first f . second g

primProg :: Prim a b -> StackProg a b
primProg p = SP (Prim p :< Nil)

instance Cartesian StackProg where
  exl = primProg Exl
  exr = primProg Exr
  dup = primProg Dup

instance Num a => NumCat StackProg a where
  addC = primProg Add
  subC = primProg Sub
  mulC = primProg Mul
  negateC = primProg Negate

instance Terminal StackProg where
  it = primProg $ Const ()

instance Show b => ConstCat StackProg b where
  unitArrow b = primProg $ Const b

-- instance Num b => LotsOfCat StackProg (StackProg a b)

progFun :: StackProg a b -> StackFun a b
progFun (SP ops) = SF (evalStackOps ops)

-- Dup, Push, Dup, Push, Const 2, Pop, Swap, Push, Exl, Pop, Swap, Mul, Pop, Swap, Push, Dup, Push, Const 3, Pop, Swap, Push, Exr, Pop, Swap, Mul, Pop, Swap, Add
ops_ :: StackOps ((Integer, Integer), z) (Integer, z)
ops_ = Prim Dup :<
  Push :<
  Prim Dup :<
  Push :<
  Prim (Const 2) :<
  Pop :<
  Prim Swap :<
  Push :<
  Prim Exl :<
  Pop :<
  Prim Swap :<
  Prim Mul :<
  Pop :<
  Prim Swap :<
  Push :<
  Prim Dup :<
  Push :<
  Prim (Const 3) :<
  Pop :<
  Prim Swap :<
  Push :<
  Prim Exr  :<
  Pop :<
  Prim Swap :<
  Prim Mul :<
  Pop :<
  Prim Swap :<
  Prim Add :<
  Nil

evalStackOps0 :: StackOps (a, ()) (b, ()) -> a -> b
evalStackOps0 ops inp = res
  where (res, ()) = evalStackOps ops (inp, ())

evalStackProg0 :: StackProg a b -> a -> b
evalStackProg0 = evalStackOps0 . unSP

