// rbtree: inserts 4,200,000 keys into a red-black tree, the value of every tenth true, and folds
// over the tree to count the true values (Reinking et al., Perceus, PLDI 2021). Its keys are 32-bit
// integers, as the paper's program has them.
import std/num/int32

type color
  Red
  Black

type tree
  Leaf
  Node(color : color, left : tree, key : int32, value : bool, right : tree)

fun red(t : tree) : bool
  match t
    Node(Red, _, _, _, _) -> True
    _ -> False

// Rebalances a black node whose left child `l` is red.
fun balance-left(l : tree, k : int32, v : bool, r : tree) : tree
  match l
    Node(_, Node(Red, a, ka, va, b), kb, vb, c) -> Node(Red, Node(Black, a, ka, va, b), kb, vb, Node(Black, c, k, v, r))
    Node(_, a, ka, va, Node(Red, b, kb, vb, c)) -> Node(Red, Node(Black, a, ka, va, b), kb, vb, Node(Black, c, k, v, r))
    Node(_, a, ka, va, b) -> Node(Black, Node(Red, a, ka, va, b), k, v, r)
    Leaf -> Leaf

// Rebalances a black node whose right child `r` is red.
fun balance-right(l : tree, k : int32, v : bool, r : tree) : tree
  match r
    Node(_, Node(Red, a, ka, va, b), kb, vb, c) -> Node(Red, Node(Black, l, k, v, a), ka, va, Node(Black, b, kb, vb, c))
    Node(_, a, ka, va, Node(Red, b, kb, vb, c)) -> Node(Red, Node(Black, l, k, v, a), ka, va, Node(Black, b, kb, vb, c))
    Node(_, a, ka, va, b) -> Node(Black, l, k, v, Node(Red, a, ka, va, b))
    Leaf -> Leaf

fun ins(t : tree, k : int32, v : bool) : tree
  match t
    Leaf -> Node(Red, Leaf, k, v, Leaf)
    Node(Red, l, kx, vx, r) ->
      if k < kx then Node(Red, ins(l, k, v), kx, vx, r)
      elif k > kx then Node(Red, l, kx, vx, ins(r, k, v))
      else Node(Red, l, k, v, r)
    Node(Black, l, kx, vx, r) ->
      if k < kx then (if red(l) then balance-left(ins(l, k, v), kx, vx, r) else Node(Black, ins(l, k, v), kx, vx, r))
      elif k > kx then (if red(r) then balance-right(l, kx, vx, ins(r, k, v)) else Node(Black, l, kx, vx, ins(r, k, v)))
      else Node(Black, l, k, v, r)

fun insert(t : tree, k : int32, v : bool) : tree
  match ins(t, k, v)
    Node(_, l, kx, vx, r) -> Node(Black, l, kx, vx, r)
    Leaf -> Leaf

fun fold(t : tree, acc : a, f : (int32, bool, a) -> e a) : e a
  match t
    Node(_, l, k, v, r) -> fold(r, f(k, v, fold(l, acc, f)), f)
    Leaf -> acc

fun make-tree(k : int32, t : tree) : div tree
  if k <= zero then t
  else
    val k' = k.dec
    make-tree(k', insert(t, k', k' % 10.int32 == zero))

pub fun main()
  val t = make-tree(4200000.int32, Leaf)
  println(t.fold(0, fn(_, v, count) if v then count + 1 else count))
