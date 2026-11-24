-- rbtree-ck: rbtree, keeping a list of every fifth tree it makes, which share most of their
-- nodes, and folding over the last to count its true values (Reinking et al., Perceus, PLDI 2021).
-- The tree's fields are strict, as the paper's version is, so that it does the same work.
{-# LANGUAGE BangPatterns #-}

module Main (main) where

data Color = Red | Black

data Tree = Leaf | Node !Color !Tree !Int !Bool !Tree

isRed :: Tree -> Bool
isRed (Node Red _ _ _ _) = True
isRed _ = False

-- | Rebalances a black node whose left child is red.
balanceLeft :: Tree -> Int -> Bool -> Tree -> Tree
balanceLeft (Node _ (Node Red a ka va b) kb vb c) k v r =
  Node Red (Node Black a ka va b) kb vb (Node Black c k v r)
balanceLeft (Node _ a ka va (Node Red b kb vb c)) k v r =
  Node Red (Node Black a ka va b) kb vb (Node Black c k v r)
balanceLeft (Node _ a ka va b) k v r = Node Black (Node Red a ka va b) k v r
balanceLeft Leaf _ _ _ = Leaf

-- | Rebalances a black node whose right child is red.
balanceRight :: Tree -> Int -> Bool -> Tree -> Tree
balanceRight l k v (Node _ (Node Red a ka va b) kb vb c) =
  Node Red (Node Black l k v a) ka va (Node Black b kb vb c)
balanceRight l k v (Node _ a ka va (Node Red b kb vb c)) =
  Node Red (Node Black l k v a) ka va (Node Black b kb vb c)
balanceRight l k v (Node _ a ka va b) = Node Black l k v (Node Red a ka va b)
balanceRight _ _ _ Leaf = Leaf

ins :: Tree -> Int -> Bool -> Tree
ins Leaf k v = Node Red Leaf k v Leaf
ins (Node Red l kx vx r) k v
  | k < kx = Node Red (ins l k v) kx vx r
  | k == kx = Node Red l k v r
  | otherwise = Node Red l kx vx (ins r k v)
ins (Node Black l kx vx r) k v
  | k < kx = if isRed l then balanceLeft (ins l k v) kx vx r else Node Black (ins l k v) kx vx r
  | k == kx = Node Black l k v r
  | isRed r = balanceRight l kx vx (ins r k v)
  | otherwise = Node Black l kx vx (ins r k v)

setBlack :: Tree -> Tree
setBlack (Node _ l k v r) = Node Black l k v r
setBlack Leaf = Leaf

insert :: Tree -> Int -> Bool -> Tree
insert t k v = if isRed t then setBlack (ins t k v) else ins t k v

fold :: (Int -> Bool -> a -> a) -> Tree -> a -> a
fold _ Leaf !acc = acc
fold f (Node _ l k v r) !acc = fold f r (f k v (fold f l acc))

-- | The trees after every fifth insertion, the last tree first.
makeTrees :: Int -> Int -> [Tree]
makeTrees n every = go n Leaf []
  where
    go 0 t trees = t : trees
    go k !t !trees =
      let t' = insert t k (k `mod` 10 == 0)
       in go (k - 1) t' (if k `mod` every == 0 then t' : trees else trees)

main :: IO ()
main = case makeTrees 4200000 5 of
  lastTree : _ -> print (fold (\_ v count -> if v then count + 1 else count) lastTree (0 :: Int))
  [] -> pure ()
