-- binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree of
-- depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
-- Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021). The tree's fields are
-- strict, as the paper's version is, so that it does the same work, and the two subtrees of a node
-- are made apart, where common-subexpression elimination would make one tree of both.
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main (main) where

import Control.Monad (forM_)
import Data.Bits (shiftL)

data Tree = Tip | Node !Tree !Tree

make :: Int -> Tree
make depth
  | depth > 0 = Node (make (depth - 1)) (make (depth - 1))
  | otherwise = Node Tip Tip

check :: Tree -> Int
check (Node l r) = check l + check r + 1
check Tip = 0

-- | The total of the checks of @count@ trees of @depth@, each made afresh.
checks :: Int -> Int -> Int -> Int
checks _ 0 !total = total
checks depth count !total = checks depth (count - 1) (total + check (make depth))

main :: IO ()
main = do
  let minDepth = 4
      maxDepth = 21
      stretch = maxDepth + 1
  putStrLn ("stretch tree of depth " ++ show stretch ++ "\t check: " ++ show (check (make stretch)))
  let !longLived = make maxDepth
  forM_ [minDepth, minDepth + 2 .. maxDepth] $ \depth -> do
    let count = 1 `shiftL` (maxDepth + minDepth - depth) :: Int
        total = checks depth count 0
    putStrLn (show count ++ "\t trees of depth " ++ show depth ++ "\t check: " ++ show total)
  putStrLn ("long lived tree of depth " ++ show maxDepth ++ "\t check: " ++ show (check longLived))
