-- cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its constants,
-- then evaluates it before and after (Reinking et al., Perceus, PLDI 2021). The expression's
-- fields are strict, as the paper's version is, so that it does the same work.
module Main (main) where

data Expr = Var !Int | Val !Int | Add !Expr !Expr | Mul !Expr !Expr

make :: Int -> Int -> Expr
make 0 v = if v == 0 then Var 1 else Val v
make n v = Add (make (n - 1) (v + 1)) (make (n - 1) (max (v - 1) 0))

appendAdd :: Expr -> Expr -> Expr
appendAdd (Add x y) b = Add x (appendAdd y b)
appendAdd a b = Add a b

appendMul :: Expr -> Expr -> Expr
appendMul (Mul x y) b = Mul x (appendMul y b)
appendMul a b = Mul a b

reassoc :: Expr -> Expr
reassoc (Add a b) = appendAdd (reassoc a) (reassoc b)
reassoc (Mul a b) = appendMul (reassoc a) (reassoc b)
reassoc e = e

fold :: Expr -> Expr
fold (Add a b) = case (fold a, fold b) of
  (Val x, Val y) -> Val (x + y)
  (Val x, Add f (Val y)) -> Add (Val (x + y)) f
  (Val x, Add (Val y) f) -> Add (Val (x + y)) f
  (a', b') -> Add a' b'
fold (Mul a b) = case (fold a, fold b) of
  (Val x, Val y) -> Val (x * y)
  (Val x, Mul f (Val y)) -> Mul (Val (x * y)) f
  (Val x, Mul (Val y) f) -> Mul (Val (x * y)) f
  (a', b') -> Mul a' b'
fold e = e

eval :: Expr -> Int
eval (Var _) = 0
eval (Val v) = v
eval (Add a b) = eval a + eval b
eval (Mul a b) = eval a * eval b

main :: IO ()
main = do
  let e = make 20 1
  print (eval e)
  print (eval (fold (reassoc e)))
