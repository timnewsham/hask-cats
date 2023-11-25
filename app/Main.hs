{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
module Main (main) where

import Prelude hiding ((.), id, sum)
import Control.Category

import Cat
import Frp
import Graph
import Stack

-- \(x,y) -> 2*x + 3*y,  on (10,100)
prog_ :: (MonoidalP k, Terminal k, ConstCat k b, NumCat k b, Num b) => (b, b) `k` b
prog_ = addC . ((mulC . (constC 2 `cross` exl) . dup) `cross` (mulC . (constC 3 `cross` exr) . dup)) . dup

testGraph :: IO ()
testGraph = do
  let graph = prog_ :: Graph (Integer, Integer) Integer
  let dot = mkCircuit "MyGraph" graph
  writeFile "graph.dot" dot
  putStr dot

testStack :: IO ()
testStack = do
    let prog = prog_ :: StackProg (Integer, Integer) Integer
    --
    print ops_
    putStrLn $ "eval stack ops: " ++ show (evalStackOps0 ops_ (10,100))
    --
    print prog
    putStrLn $ "eval stack prog: " ++ show (evalStackProg0 prog (10,100))

testFrp :: IO ()
testFrp = do
    let t1 = NoBound (TimeT 3) :: FTime
    let t2 = NoBound (TimeT 5) :: FTime
    print $ mconcat [t1, t2]
    let f1 = Fut (t1, 23) :: Future Integer
    let f2 = Fut (t2, 25) :: Future Integer
    print $ mconcat [f1, f2]

main :: IO ()
main = do
    testStack
    testFrp
    testGraph
