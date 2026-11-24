// cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its constants,
// then evaluates it before and after (Reinking et al., Perceus, PLDI 2021).

type expr
  Var(name : int)
  Val(value : int)
  Add(left : expr, right : expr)
  Mul(left : expr, right : expr)

fun make(n : int, v : int) : div expr
  if n == 0 then (if v == 0 then Var(1) else Val(v))
  else Add(make(n - 1, v + 1), make(n - 1, max(v - 1, 0)))

fun append-add(a : expr, b : expr) : expr
  match a
    Add(x, y) -> Add(x, append-add(y, b))
    _ -> Add(a, b)

fun append-mul(a : expr, b : expr) : expr
  match a
    Mul(x, y) -> Mul(x, append-mul(y, b))
    _ -> Mul(a, b)

fun reassoc(e : expr) : expr
  match e
    Add(a, b) -> append-add(reassoc(a), reassoc(b))
    Mul(a, b) -> append-mul(reassoc(a), reassoc(b))
    _ -> e

fun fold(e : expr) : expr
  match e
    Add(a, b) ->
      match (fold(a), fold(b))
        (Val(x), Val(y)) -> Val(x + y)
        (Val(x), Add(f, Val(y))) -> Add(Val(x + y), f)
        (Val(x), Add(Val(y), f)) -> Add(Val(x + y), f)
        (a', b') -> Add(a', b')
    Mul(a, b) ->
      match (fold(a), fold(b))
        (Val(x), Val(y)) -> Val(x * y)
        (Val(x), Mul(f, Val(y))) -> Mul(Val(x * y), f)
        (Val(x), Mul(Val(y), f)) -> Mul(Val(x * y), f)
        (a', b') -> Mul(a', b')
    _ -> e

fun eval(e : expr) : int
  match e
    Var(_) -> 0
    Val(v) -> v
    Add(a, b) -> eval(a) + eval(b)
    Mul(a, b) -> eval(a) * eval(b)

pub fun main()
  val e = make(20, 1)
  println(eval(e))
  println(eval(fold(reassoc(e))))
