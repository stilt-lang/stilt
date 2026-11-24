-- nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each partial
-- placement sharing the rows below it with the others that extend it, and counts them (Reinking et
-- al., Perceus, PLDI 2021). Each row's boards are built in full before the next row, as the
-- paper's version does. A board is the columns of its queens, the last placed first.
module Main (main) where

import Data.List (foldl')

-- | Whether a queen in column @queen@ is safe from those of a board, the nearest @diag@ rows away.
safe :: Int -> Int -> [Int] -> Bool
safe _ _ [] = True
safe queen diag (q : rest) =
  queen /= q && queen /= q + diag && queen /= q - diag && safe queen (diag + 1) rest

-- | Every board with a queen added in a safe column of @n@.
extend :: Int -> [[Int]] -> [[Int]]
extend n = foldl' place []
  where
    place next board = foldl' (add board) next [n, n - 1 .. 1]
    add board next queen = if safe queen 1 board then (queen : board) : next else next

queens :: Int -> Int
queens n = length (go n [[]])
  where
    go 0 boards = boards
    go i boards = go (i - 1) $! extend n boards

main :: IO ()
main = print (queens 13)
