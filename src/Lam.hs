{-# LANGUAGE GADTs #-}

module Lam (
    Lam (..)
    , Val (..)
    , simpl
    , eval
    ) where

import Prelude hiding ((.))
import Control.Category
import Data.Kind
import Data.List
import qualified Data.Map as M

import GHC.Exts (Any)
import Unsafe.Coerce

data Lam :: Type -> Type where
    Var :: String -> Lam a
    LNum :: (Show a, Num a) => a -> Lam a
    Neg :: Num a => Lam a -> Lam a
    Add :: Num a => Lam a -> Lam a -> Lam a
    Sub :: Num a => Lam a -> Lam a -> Lam a
    Mul :: Num a => Lam a -> Lam a -> Lam a
    Abs :: String -> Lam b -> Lam (a -> b) -- guh! want a to be bound to name!
    App :: Lam (a -> b) -> Lam a -> Lam b

instance (Show a, Num a) => Num (Lam a) where
    fromInteger = LNum . fromInteger
    negate = Neg
    (+) = Add
    (-) = Sub
    (*) = Mul
    abs = error "no abs"
    signum = error "no signum"

parens :: [String] -> String
parens xs = "(" ++ intercalate " " xs ++ ")"

instance Show (Lam a) where
  show (Var x) = parens ["Var", x]
  show (LNum n) = parens ["LNum", show n]
  show (Neg a) = parens ["Neg", show a]
  show (Add a b) = parens ["Add", show a, show b]
  show (Sub a b) = parens ["Sub", show a, show b]
  show (Mul a b) = parens ["Mul", show a, show b]
  show (Abs n e) = parens ["Abs", n, show e]
  show (App a b) = parens ["App", show a, show b]


-- Env binds maps names to values
type Env = M.Map String Any -- Any converts to (Val a)

empty :: Env
empty = M.empty

get :: Env -> String -> a -> a
get env nm def = case M.lookup nm env of
                    Nothing -> def
                    Just val -> unsafeCoerce val

bind :: Env -> String -> a -> Env
bind env nm val = M.insert nm (unsafeCoerce val) env

getExpr :: Env -> String -> Lam a -> Lam a
getExpr = get

bindExpr :: Env -> String -> Lam a -> Env
bindExpr = bind

simpl :: Env -> Lam a -> Lam a
simpl env (Var nm) = getExpr env nm (Var nm)
simpl _ (LNum n) = LNum n
simpl env (Neg a) = Neg (simpl env a)
simpl env (Add a b) = Add (simpl env a) (simpl env b)
simpl env (Sub a b) = Sub (simpl env a) (simpl env b)
simpl env (Mul a b) = Mul (simpl env a) (simpl env b)
simpl env (Abs nm e) = Abs nm (simpl env e)
simpl env (App f x) = case simpl env f of
                        Abs nm e -> let env' = bindExpr env nm x in simpl env' e
                        f' -> App f' (simpl env x)

data Val :: Type -> Type where
    ValNum :: (Show a, Num a) => a -> Val a
    ValFunc :: (Val a -> Val b) -> Val (a -> b)

instance Show (Val a) where
  show (ValNum x) = parens ["ValNum", show x]
  show (ValFunc x) = parens ["ValFunc"]

getVal :: Env -> String -> Val a -> Val a
getVal = get

bindVal :: Env -> String -> Val a -> Env
bindVal = bind

unaryValOp :: Num a => (a -> a) -> Val a -> Val a
unaryValOp op (ValNum x) = ValNum $ op x

binaryValOp :: Num a => (a -> a -> a) -> Val a -> Val a -> Val a
binaryValOp op (ValNum a) (ValNum b) = ValNum $ a `op` b

eval :: Env -> Lam a -> Val a
eval env (Var nm) = getVal env nm (error $ "unknown variable " ++ nm)
eval _ (LNum n) = ValNum n
eval env (Neg a) = unaryValOp negate (eval env a)
eval env (Add a b) = binaryValOp (+) (eval env a) (eval env b)
eval env (Sub a b) = binaryValOp (-) (eval env a) (eval env b)
eval env (Mul a b) = binaryValOp (*) (eval env a) (eval env b)
eval env (Abs nm e) = evalLam env (Abs nm e)
  where
    evalLam :: Env -> Lam (a -> b) -> Val (a -> b)
    evalLam env (Abs nm e) = ValFunc (\inp -> let env' = bindVal env nm inp in eval env' e)
eval env (App f x) = let (ValFunc f') = eval env f in f' (eval env x)

l_id :: Lam (a -> a)
l_id = "x" `Abs` Var "x"

l_dot :: Lam ((b -> c) -> (a -> b) -> (a -> c))
l_dot = "f" `Abs` ("g" `Abs` ("x" `Abs` (Var "f" `App` (Var "g" `App` Var "x"))))

l_double :: (Show a, Num a) => Lam (a -> a)
l_double = "x" `Abs` (Var "x" + Var "x")

l_square :: (Show a, Num a) => Lam (a -> a)
l_square = "x" `Abs` (Var "x" * Var "x")

main = do
    -- let test = ("x" `Abs` Var "x") `App` LNum 5
    -- let test = App (Abs "x" (Var "x" `Mul` Var "x")) (LNum 5)
    -- let test = Abs "x" (Var "x" `Mul` Var "x")
    -- \x y -> 2*x + 3*y
    -- let f = "x" `Abs` ("y" `Abs` (LNum 2 * Var "x" + LNum 3 * Var "y"))
    -- let test = f `App` LNum 100 `App` LNum 10
    let test = l_dot `App` l_double `App` l_square `App` LNum 10
    putStr "expr: "
    print test
    putStr "val: "
    print $ eval empty test

    let test' = simpl empty test
    putStr "simp: "
    print test'
    putStr "val: "
    print $ eval empty test'
