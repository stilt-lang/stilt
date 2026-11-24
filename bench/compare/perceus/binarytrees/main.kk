// binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree of
// depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
// Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021).

type tree
  Tip
  Node(left : tree, right : tree)

fun make(depth : int) : div tree
  if depth > 0 then Node(make(depth - 1), make(depth - 1)) else Node(Tip, Tip)

fun check(t : tree) : div int
  match t
    Node(l, r) -> check(l) + check(r) + 1
    Tip -> 0

fun checks(depth : int, count : int, total : int) : div int
  if count == 0 then total else checks(depth, count - 1, total + check(make(depth)))

fun depths(depth : int, min-depth : int, max-depth : int) : <console, div> ()
  if depth <= max-depth then
    val count = 2 ^ (max-depth + min-depth - depth)
    println(show(count) ++ "\t trees of depth " ++ show(depth) ++ "\t check: " ++ show(checks(depth, count, 0)))
    depths(depth + 2, min-depth, max-depth)

pub fun main()
  val min-depth = 4
  val max-depth = 21
  val stretch = max-depth + 1
  println("stretch tree of depth " ++ show(stretch) ++ "\t check: " ++ show(check(make(stretch))))
  val long-lived = make(max-depth)
  depths(min-depth, min-depth, max-depth)
  println("long lived tree of depth " ++ show(max-depth) ++ "\t check: " ++ show(check(long-lived)))
