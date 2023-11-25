{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Graph (
  Graph
  , mkCircuit
  ) where

import Prelude hiding ((.), id, log)
import Control.Applicative
import Control.Category
import qualified Data.Map as Map
import Data.Kind
import Data.List (intercalate, stripPrefix)
import Data.Maybe
import Control.Monad.State
import Text.Printf

import Cat

type Port = Int

data Ports :: Type -> Type where
  UnitP :: Ports ()
  BoolP :: Port -> Ports Bool
  IntP :: Port -> Ports Integer
  DoubleP :: Port -> Ports Double
  PairP :: Ports a -> Ports b -> Ports (a, b)
  --FunP :: Graph a b -> Ports (a -> b)  -- a \doublearrow b

data Comp = forall a b . Comp String (Ports a) (Ports b) -- op name, ins, outs

type GraphM = State (Port, [Comp])

data Graph a b = Graph (Ports a -> GraphM (Ports b))

instance Category Graph where
  -- type Ok Graph a = GenPorts a
  id = Graph return
  Graph g . Graph f = Graph (g <=< f)

instance Cartesian Graph where
  exl = Graph (\(PairP a _) -> return a)
  exr = Graph (\(PairP _ b) -> return b)
  dup = Graph (\x -> return (PairP x x))

instance MonoidalP Graph where
  -- using the wrong liftA2 here?
  -- Graph f `cross` Graph g = Graph (liftA2 (liftA2 PairP) f g)
  Graph f `cross` Graph g = Graph (\(PairP x y) -> do { fx <- f x; gy <- g y; return (PairP fx gy) })
  first f = f `cross` id
  second g = id `cross` g

genPort :: GraphM Port
genPort = do { (o, comps) <- get; put (o + 1, comps); return o }

class GenPorts a where
  genPorts :: GraphM (Ports a)

instance GenPorts () where genPorts = return UnitP
instance GenPorts Bool where genPorts = fmap BoolP genPort
instance GenPorts Integer where genPorts = fmap IntP genPort
instance GenPorts Double where genPorts = fmap DoubleP genPort

instance (GenPorts a, GenPorts b) => GenPorts (a, b) where
  genPorts = liftA2 PairP genPorts genPorts

genComp :: GenPorts b => String -> Graph a b
genComp name = Graph (\a -> do { b <- genPorts; modify (second (Comp name a b :)); return b } )

instance Terminal Graph where
  it = genComp "const ()"

instance (Show b, GenPorts b) => ConstCat Graph b where
  unitArrow x = genComp $ "const " ++ show x

-- constC :: (GenPorts b, Show b) => b -> (a `Graph` b)
-- constC x = genComp $ "const " ++ show x

instance (GenPorts a) => NumCat Graph a where
  negateC = genComp "negate"
  addC = genComp "add"
  subC = genComp "sub"
  mulC = genComp "mul"

-- \(x,y) -> 2*x + 3*y
-- graph_ :: Graph (Integer, Integer) Integer
-- graph_ = addC . ((mulC . (constC 2 `cross` exl) . dup) `cross` (mulC . (constC 3 `cross` exr) . dup)) . dup

--graph_ :: Graph (Integer, Integer) Integer
-- graph_ = addC . (negateC `cross` id)
--graph_ = addC . (mulC `cross` subC) . dup

getPorts :: Ports a -> [Port]
getPorts UnitP = []
getPorts (BoolP n) = [n]
getPorts (IntP n) = [n]
getPorts (DoubleP n) = [n]
getPorts (PairP p1 p2) = getPorts p1 ++ getPorts p2

instance Show (Ports a) where
  show UnitP = "empty"
  show (BoolP n) = "bool:" ++ show n
  show (IntP n) = "int:" ++ show n
  show (DoubleP n) = "double:" ++ show n
  show (PairP p1 p2) = "(" ++ show p1 ++ ", " ++ show p2 ++ ")"

instance Show Comp where
  show (Comp name pa pb) = "[" ++ name ++ " " ++ show pa ++ " " ++ show pb ++ "]"

ints :: [Int]
ints = [1..]

nodeLabel :: Comp -> String
nodeLabel (Comp name ins outs) = wrap "[label=\""  "\"]" [inlabels, name, outlabels]
  where
        -- variant that shows the edge number
        --inPortLabel (idx, edge) = printf "<in_%d_%d> %d" idx edge edge
        --outPortLabel edge = printf "<out_%d> %d" edge edge
        -- variant that doesnt show the edge number
        inPortLabel (idx, edge) = printf "<in_%d_%d>" idx edge
        outPortLabel edge = printf "<out_%d>" edge
        clean = filter (/= "")
        wrap pref suff xs = 
          let ys = clean xs in 
            if ys == [] 
               then "" 
               else printf "%s%s%s" pref (intercalate " | " ys) suff
        inlabels = wrap "{ " " }" (map inPortLabel $ zip ints $ getPorts ins)
        outlabels = wrap "{ " " }" (map outPortLabel $ getPorts outs)

mkCircuit :: (GenPorts a) => String -> Graph a b -> String -- IO ()
mkCircuit title g = flip execState "" $ do
    let log = modify . (flip (++))
    let nodeName compIdx = printf "node_%d" compIdx :: String
    let inPortName compIdx idx edge = printf "%s:in_%d_%d" (nodeName compIdx) idx edge :: String
    let outPortName compIdx edge = printf "%s:out_%d" (nodeName compIdx) edge :: String
    let removeConstInputs (Comp name ins outs) = if isJust $ stripPrefix "const" name then (Comp name UnitP outs) else (Comp name ins outs)

    -- augment graph with input and output node
    let (Graph g') = (genComp "ouput" :: Graph b ()) . g . genComp "input"
    let (_, comps) = execState (g' UnitP) (0, [])
    let comps2 = map removeConstInputs comps
    let numberedComponents = zip ints comps2
    let mapInsToNodes = flip execState Map.empty (do
                          forM_ numberedComponents (\(compNum, (Comp _ _ outs)) ->
                            forM_ (getPorts outs) (\port ->
                              modify $ Map.insert port compNum
                              )
                            )
                          )

    log $ printf "\n"
    log $ printf "digraph %s {\n" title
    log $ printf "  rankdir=LR;\n"
    log $ printf "  node [shape=Mrecord];\n"
    log $ printf "  edge [fontsize=8,fontcolor=indigo];\n"

    -- generate each node name
    forM_ numberedComponents (\(compNum, comp) ->
      log $ printf "  %s %s;\n" (nodeName compNum) (nodeLabel comp)
      )

    -- Generate edges into each input
    forM_ numberedComponents (\(compNum, (Comp _ ins _)) ->
      forM_ (zip ints $ getPorts ins) (\(inIdx, port) -> do
        case Map.lookup port mapInsToNodes of
          -- Nothing -> return ()
          Nothing -> log $ printf "dont know what to do with %s\n" (show port)
          Just targCompNum -> log $ printf "  %s -> %s;\n" (outPortName targCompNum port) (inPortName compNum inIdx port)
        )
      )

    log $ printf "}\n"
