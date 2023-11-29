{-# LANGUAGE GADTs, DataKinds #-}

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

import qualified Lam as STLC

data Witness a = MkWitness
data Unk = Unk
data Err = Err

data Lab = LErr | LUnk | LInt | LFun deriving Show

data WType :: Type -> Type where
    WErr :: WType Err
    WUnk :: WType Unk
    WInt :: WType Int
    WFun :: WType a -> WType b -> WType (a->b)

data Typ where
    TErr :: WType a -> String -> Typ
    TUnk :: WType a -> Typ
    TInt :: WType a -> Typ
    TFun :: WType a -> Typ -> Typ -> Typ

withWitness :: Typ -> (forall a . WType a -> r) -> r
withWitness (TErr w _) f = f w
withWitness (TUnk w) f = f w
withWitness (TInt w) f = f w
withWitness (TFun w _ _) f = f w

-- More convenient constructors for Typ
tErr msg = TErr WErr msg
tUnk = TUnk WUnk
tInt = TInt WInt
tFun t1 t = withWitness t1 (\w1 -> withWitness t (\w2 -> TFun (WFun w1 w2) t1 t))

instance Show Typ where
    showsPrec d (TErr _ e) = showParen (d > 0) $ showString "Terr"
    showsPrec d (TUnk _) = showString "TUnk"
    showsPrec d (TInt _) = showString "TInt"
    showsPrec d (TFun _ a b) = showParen (d > 0) $ showsPrec (d+1) a . showString "->" . showsPrec (d+1) b


data Lam where
    Var :: Typ -> String -> Lam
    LNum :: (Show a, Num a, Enum a) => Typ -> a -> Lam
    Neg :: Typ -> Lam -> Lam
    Add :: Typ -> Lam -> Lam -> Lam
    Sub :: Typ -> Lam -> Lam -> Lam
    Mul :: Typ -> Lam -> Lam -> Lam
    Abs :: Typ -> Lam -> Lam -> Lam -- Note: we require first item to be a Var. not enforced by types! fixme.
    App :: Typ -> Lam -> Lam -> Lam

instance Num Lam where
    fromInteger = LNum tUnk . fromInteger
    negate = Neg tUnk
    (+) = Add tUnk
    (-) = Sub tUnk
    (*) = Mul tUnk
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

unify :: Typ -> Typ -> Typ
unify a@(TErr w e) _ = a
unify _ b@(TErr w e) = b
unify (TUnk w) b = b
unify a (TUnk w) = a
unify a@(TInt wa) (TInt wb) = a
unify (TFun w a b) (TFun w' a' b') = tFun aa' bb'
    where aa' = unify a a'
          bb' = unify b b'
unify a a' = tErr $ printf "unify: %s is not %s" (show a) (show a')

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
    return $ getTyp env nm tUnk

bindTyp2 :: String -> Typ -> State (Env Typ) ()
bindTyp2 nm ty = modify $ M.insert nm ty

unifyLam :: Typ -> Lam -> State (Env Typ) Lam
unifyLam ty (Var ty' nm) = do
    nmTy <- getTyp2 nm
    let uty = ty `unify` ty' `unify` nmTy
    bindTyp2 nm uty
    return $ Var uty nm
unifyLam ty (LNum ty' a) = return $ LNum (tInt `unify` ty `unify` ty') a
unifyLam ty (Neg ty' a) = do
    let uty = tInt `unify` ty `unify` ty' 
    a' <- unifyLam uty a
    return $ Neg uty a'
unifyLam ty (Add ty' a b) = do
    let uty = tInt `unify` ty `unify` ty'
    a' <- unifyLam uty a
    b' <- unifyLam uty b
    return $ Add uty a' b'
unifyLam ty (Sub ty' a b) =do
    let uty = tInt `unify` ty `unify` ty'
    a' <- unifyLam uty a
    b' <- unifyLam uty b
    return $ Sub uty a' b'
unifyLam ty (Mul ty' a b) = do
    let uty = tInt `unify` ty `unify` ty'
    a' <- unifyLam uty a
    b' <- unifyLam uty b
    return $ Mul uty a' b'
unifyLam ty (Abs ty' arg@(Var argTy nm) e) = shadowing nm $ do
    let uty = tFun argTy tUnk `unify` ty `unify` ty'
    bindTyp2 nm (argumentType uty)
    e' <- unifyLam (resultType uty) e
    argTy' <- getTyp2 nm
    arg' <- unifyLam tUnk arg
    let uty' = tFun (lamType arg') (lamType e') `unify` uty
    return $ Abs uty' arg' e'
unifyLam ty (App ty' f x) = do
    let uty = ty `unify` ty'
    x' <- unifyLam tUnk x
    f' <- unifyLam (tFun (lamType x') uty) f
    let uty' = uty `unify` resultType (lamType f')
    return $ App uty' f' x'

resultType (TFun w a b) = b
resultType _ = tUnk

argumentType (TFun w a b) = a
argumentType _ = tUnk

typeCheck e = evalState (unifyLam tUnk e) empty

stlc :: WType a -> Lam -> STLC.Lam a
stlc _ (Var ty nm) = STLC.Var nm
stlc WInt (LNum ty x) = STLC.LNum $ fromEnum x
stlc WInt (Neg ty e) = STLC.Neg (stlc WInt e)
stlc WInt (Add ty e1 e2) = STLC.Add (stlc WInt e1) (stlc WInt e2)
stlc WInt (Sub ty e1 e2) = STLC.Add (stlc WInt e1) (stlc WInt e2)
stlc WInt (Mul ty e1 e2) = STLC.Add (stlc WInt e1) (stlc WInt e2)
stlc (WFun w1 w2) (Abs _ (Var _ nm) e) = STLC.Abs nm (stlc w2 e)
stlc WErr l = case lamType l of (TErr _ msg) -> error $ msg ++ " for " ++ show l
stlc WUnk l = error $ "unknown type for " ++ show l

withStlc :: Lam -> (forall a. STLC.Lam a -> r) -> r
withStlc l f = withWitness (lamType l) (\w -> f (stlc w l))

main = do
    let abs nm = Abs tUnk (Var tUnk nm)
    let app = App tUnk
    let var = Var tUnk
    let lnum = LNum tUnk
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
    -- let f = "x" `abs` ("y" `abs` (lnum 2 * var "x" + lnum 3 * var "y"))
    -- let test = f
    --let test = f `app` lnum 100 `app` lnum 10
    let test = l_dot `app` l_double `app` l_square `app` lnum 10
    -- let test = l_bad2 -- XXX doesnt behave as expected
    let test = "x" `abs` ("y" `abs` (var "x" + lnum 3))
    -- let test = "x" `abs` (var "x" + lnum 3)
    putStrLn $ "expr: " ++ show test
    let typed = typeCheck test
    -- putStrLn $ "typed: " ++ showTypes typed
    putStrLn $ "type: " ++ show (lamType typed)

    let test' = simpl empty test
    putStrLn $ "simp: " ++ show test'
    let typed' = typeCheck test'
    -- putStrLn $ "typed: " ++ showTypes typed'
    putStrLn $ "type: " ++ show (lamType typed')

    --withWitness (lamType typed) (\w -> print $ stlc w typed)
    withStlc typed print
    withStlc typed' print
