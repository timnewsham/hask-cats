{-# LANGUAGE GADTs #-}

module UTLam (
    Lam (..)
    , simpl
    ) where

import Prelude hiding ((.))
import Control.Category
import Control.Monad.State
import Data.Kind
import Data.List
import qualified Data.Map as M
import Text.Printf

import qualified Lam as St

data Lam where
    Var :: Typ -> String -> Lam
    LNum :: (Show a, Num a) => Typ -> a -> Lam
    Neg :: Typ -> Lam -> Lam
    Add :: Typ -> Lam -> Lam -> Lam
    Sub :: Typ -> Lam -> Lam -> Lam
    Mul :: Typ -> Lam -> Lam -> Lam
    Abs :: Typ -> Lam -> Lam -> Lam -- Note: we require first item to be a Var. not enforced by types! fixme.
    App :: Typ -> Lam -> Lam -> Lam

instance Num Lam where
    fromInteger = LNum TUnk . fromInteger
    negate = Neg TUnk
    (+) = Add TUnk
    (-) = Sub TUnk
    (*) = Mul TUnk
    abs = error "no abs"
    signum = error "no signum"

parens :: [String] -> String
parens xs = "(" ++ intercalate " " xs ++ ")"

-- Show without types
instance Show Lam where
  show (Var ty x) = parens ["Var", x]
  show (LNum ty n) = parens ["LNum", show n]
  show (Neg ty a) = parens ["Neg", show a]
  show (Add ty a b) = parens ["Add", show a, show b]
  show (Sub ty a b) = parens ["Sub", show a, show b]
  show (Mul ty a b) = parens ["Mul", show a, show b]
  show (Abs ty nm e) = parens ["Abs", show nm, show e]
  show (App ty a b) = parens ["App", show a, show b]

-- Show with types
showTypes :: Lam -> String
showTypes (Var ty x) = printf "%s::%s" x (show ty)
showTypes (LNum ty n) = printf "%s::%s" (show n) (show ty)
showTypes (Neg ty a) = printf "(Neg::%s %s)" (show ty) (showTypes a)
showTypes (Add ty a b) = printf "(Add::%s %s %s)" (show ty) (showTypes a) (showTypes b)
showTypes (Sub ty a b) = printf "(Sub::%s %s %s)" (show ty) (showTypes a) (showTypes b)
showTypes (Mul ty a b) = printf "(Mul::%s %s %s)" (show ty) (showTypes a) (showTypes b)
showTypes (Abs ty nm e) = printf "(\\%s -> %s)::%s" (showTypes nm) (showTypes e) (show ty)
showTypes (App ty a b) = printf "(%s %s)::%s" (showTypes a) (showTypes b) (show ty)

type Env a = M.Map String a

empty :: Env a
empty = M.empty

getEnv :: Env a -> String -> a -> a
getEnv env nm def = case M.lookup nm env of
                    Nothing -> def
                    Just val -> val

bindEnv :: Env a -> String -> a -> Env a
bindEnv env nm val = M.insert nm val env

getExpr :: Env Lam -> String -> Lam -> Lam
getExpr = getEnv

bindExpr :: Env Lam -> String -> Lam -> Env Lam
bindExpr = bindEnv

simpl :: Env Lam -> Lam -> Lam
simpl env (Var ty nm) = getExpr env nm (Var ty nm)
simpl _ (LNum ty n) = LNum ty n
simpl env (Neg ty a) = Neg ty (simpl env a)
simpl env (Add ty a b) = Add ty (simpl env a) (simpl env b)
simpl env (Sub ty a b) = Sub ty (simpl env a) (simpl env b)
simpl env (Mul ty a b) = Mul ty (simpl env a) (simpl env b)
simpl env (Abs ty nm e) = Abs ty nm (simpl env e)
simpl env (App ty f x) = case simpl env f of
                            Abs ty (Var _ nm) e -> let env' = bindExpr env nm x in simpl env' e
                            f' -> App ty f' (simpl env x)

data Typ where
    TErr :: String -> Typ
    TUnk :: Typ
    TInt :: Typ
    TFun :: Typ -> Typ -> Typ

instance Show Typ where
    showsPrec d (TErr e) = showParen (d > 0) $ showString "Terr"
    showsPrec d TUnk = showString "TUnk"
    showsPrec d TInt = showString "TInt"
    showsPrec d (TFun a b) = showParen (d > 0) $ showsPrec (d+1) a . showString "->" . showsPrec (d+1) b

unify :: Typ -> Typ -> Typ
unify (TErr e) _ = TErr e
unify _ (TErr e) = TErr e
unify TUnk b = b
unify b TUnk = b
unify TInt TInt = TInt
unify (TFun a b) (TFun a' b') = TFun (unify a a') (unify b b')
unify a a' = TErr $ printf "unify: %s is not %s" (show a) (show a')


getTyp :: Env Typ -> String -> Typ -> Typ
getTyp = getEnv

bindTyp :: Env Typ -> String -> Typ -> Env Typ
bindTyp = bindEnv

lamType (Var ty _) = ty
lamType (LNum ty _) = ty
lamType (Neg ty _) = ty
lamType (Add ty _ _) = ty
lamType (Sub ty _ _) = ty
lamType (Mul ty _ _) = ty
lamType (Abs ty _ _) = ty
lamType (App ty _ _) = ty

-- shadowing saves and restores the original value for an item in
-- the environment so it can be shadowed by another value in prog.
shadowing :: String -> State (Env Typ) a -> State (Env Typ) a
shadowing nm prog = do
    orig <- gets $ M.lookup nm
    r <- prog
    modify $ M.update (const orig) nm
    return r

getTyp2 :: String -> State (Env Typ) Typ
getTyp2 nm = do
    env <- get
    return $ getTyp env nm TUnk

bindTyp2 :: String -> Typ -> State (Env Typ) ()
bindTyp2 nm ty = modify $ M.insert nm ty

unifyDown2 :: Typ -> Lam -> State (Env Typ) Lam
unifyDown2 ty (Var ty' nm) = do
    nmTy <- getTyp2 nm
    let uty = ty `unify` ty' `unify` nmTy
    bindTyp2 nm uty
    return $ Var uty nm
unifyDown2 ty (LNum ty' a) = return $ LNum (TInt `unify` ty `unify` ty') a
unifyDown2 ty (Neg ty' a) = do
    let uty = TInt `unify` ty `unify` ty' 
    a' <- unifyDown2 uty a
    return $ Neg uty a'
unifyDown2 ty (Add ty' a b) = do
    let uty = TInt `unify` ty `unify` ty'
    a' <- unifyDown2 uty a
    b' <- unifyDown2 uty b
    return $ Add uty a' b'
unifyDown2 ty (Sub ty' a b) =do
    let uty = TInt `unify` ty `unify` ty'
    a' <- unifyDown2 uty a
    b' <- unifyDown2 uty b
    return $ Sub uty a' b'
unifyDown2 ty (Mul ty' a b) = do
    let uty = TInt `unify` ty `unify` ty'
    a' <- unifyDown2 uty a
    b' <- unifyDown2 uty b
    return $ Mul uty a' b'
unifyDown2 ty (Abs ty' arg@(Var argTy nm) e) = shadowing nm $ do
    bindTyp2 nm argTy
    e' <- unifyDown2 TUnk e
    argTy' <- getTyp2 nm
    arg' <- unifyDown2 TUnk arg
    let uty = TFun (lamType arg') (lamType e') `unify` ty `unify` ty'
    return $ Abs uty arg' e'
unifyDown2 ty (App ty' f x) = do
    let uty = ty `unify` ty'
    x' <- unifyDown2 TUnk x
    f' <- unifyDown2 (TFun (lamType x') uty) f
    return $ App uty f' x'

ud2 e = evalState (unifyDown2 TUnk e) empty

main = do
    let abs nm = Abs TUnk (Var TUnk nm)
    let app = App TUnk
    let var = Var TUnk
    let lnum = LNum TUnk
    let l_id = "x" `abs` var "x"
    let l_dot = "f" `abs` ("g" `abs` ("x" `abs` (var "f" `app` (var "g" `app` var "x"))))
    let l_double = "x" `abs` (var "x" + var "x")
    let l_square = "x" `abs` (var "x" * var "x")
    let l_bad = "x" `abs` (var "x" `app` var "x")
    let l_bad2 = l_bad `app` l_bad

    -- let test = ("x" `abs` var "x") `app` lnum 5
    -- let test = App (Abs "x" (var "x" `Mul` var "x")) (lnum 5)
    -- let test = Abs "x" (var "x" `Mul` var "x")
    -- \x y -> 2*x + 3*y
    let f = "x" `abs` ("y" `abs` (lnum 2 * var "x" + lnum 3 * var "y"))
    let test = f `app` lnum 100 `app` lnum 10
    --let test = l_dot `app` l_double `app` l_square `app` lnum 10
    -- let test = l_bad2 -- XXX doesnt behave as expected
    --let test = "x" `abs` ("y" `abs` (var "x" + lnum 3))
    -- let test = "x" `abs` (var "x" + lnum 3)
    putStr "expr: "
    print test
    let test' = ud2 test
    putStrLn $ "type: " ++ showTypes test'
    let test'' = ud2 test'
    putStrLn $ "type: " ++ showTypes test''

    let test' = simpl empty test
    putStr "simp: "
    print test'
