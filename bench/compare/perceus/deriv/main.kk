// deriv: differentiates x^x ten times, simplifying each derivative as it is built, and prints the
// size of each (Reinking et al., Perceus, PLDI 2021).

type expr
  Val(value : int)
  Var(name : string)
  Add(left : expr, right : expr)
  Mul(left : expr, right : expr)
  Pow(base : expr, exponent : expr)
  Ln(arg : expr)

fun pown(a : int, n : int) : div int
  if n <= 0 then 1 else a * pown(a, n - 1)

fun add(a : expr, b : expr) : div expr
  match (a, b)
    (Val(n), Val(m)) -> Val(n + m)
    (Val(0), f) -> f
    (f, Val(0)) -> f
    (f, Val(n)) -> add(Val(n), f)
    (Val(n), Add(Val(m), f)) -> add(Val(n + m), f)
    (f, Add(Val(n), g)) -> add(Val(n), add(f, g))
    (Add(f, g), h) -> add(f, add(g, h))
    (f, g) -> Add(f, g)

fun mul(a : expr, b : expr) : div expr
  match (a, b)
    (Val(n), Val(m)) -> Val(n * m)
    (Val(0), _) -> Val(0)
    (_, Val(0)) -> Val(0)
    (Val(1), f) -> f
    (f, Val(1)) -> f
    (f, Val(n)) -> mul(Val(n), f)
    (Val(n), Mul(Val(m), f)) -> mul(Val(n * m), f)
    (f, Mul(Val(n), g)) -> mul(Val(n), mul(f, g))
    (Mul(f, g), h) -> mul(f, mul(g, h))
    (f, g) -> Mul(f, g)

fun pow(a : expr, b : expr) : div expr
  match (a, b)
    (Val(m), Val(n)) -> Val(pown(m, n))
    (_, Val(0)) -> Val(1)
    (f, Val(1)) -> f
    (Val(0), _) -> Val(0)
    (f, g) -> Pow(f, g)

fun ln(e : expr) : expr
  match e
    Val(1) -> Val(0)
    f -> Ln(f)

// The derivative of `e` by `x`.
fun d(x : string, ^e : expr) : div expr
  match e
    Val(_) -> Val(0)
    Var(y) -> if x == y then Val(1) else Val(0)
    Add(f, g) -> add(d(x, f), d(x, g))
    Mul(f, g) -> add(mul(f, d(x, g)), mul(g, d(x, f)))
    Pow(f, g) -> mul(pow(f, g), add(mul(mul(g, d(x, f)), pow(f, Val(-1))), mul(ln(f), d(x, g))))
    Ln(f) -> mul(d(x, f), pow(f, Val(-1)))

fun count(^e : expr) : int
  match e
    Val(_) -> 1
    Var(_) -> 1
    Add(f, g) -> count(f) + count(g)
    Mul(f, g) -> count(f) + count(g)
    Pow(f, g) -> count(f) + count(g)
    Ln(f) -> count(f)

fun derive(i : int, f : expr) : <console, div> ()
  if i <= 10 then
    val f' = d("x", f)
    println(show(i) ++ " count: " ++ show(count(f')))
    derive(i + 1, f')

pub fun main()
  val x = Var("x")
  derive(1, pow(x, x))
  println("done")
