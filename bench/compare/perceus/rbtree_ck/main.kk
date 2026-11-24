// rbtree-ck: rbtree, keeping a list of every fifth tree it makes, which share most of their nodes,
// and folding over the last to count its true values (Reinking et al., Perceus, PLDI 2021).

type color
  Red
  Black

type tree
  Leaf
  Node(color : color, left : tree, key : int, value : bool, right : tree)

fun red(t : tree) : bool
  match t
    Node(Red, _, _, _, _) -> True
    _ -> False

// Rebalances a black node whose left child `l` is red.
fun balance-left(l : tree, k : int, v : bool, r : tree) : tree
  match l
    Node(_, Node(Red, a, ka, va, b), kb, vb, c) -> Node(Red, Node(Black, a, ka, va, b), kb, vb, Node(Black, c, k, v, r))
    Node(_, a, ka, va, Node(Red, b, kb, vb, c)) -> Node(Red, Node(Black, a, ka, va, b), kb, vb, Node(Black, c, k, v, r))
    Node(_, a, ka, va, b) -> Node(Black, Node(Red, a, ka, va, b), k, v, r)
    Leaf -> Leaf

// Rebalances a black node whose right child `r` is red.
fun balance-right(l : tree, k : int, v : bool, r : tree) : tree
  match r
    Node(_, Node(Red, a, ka, va, b), kb, vb, c) -> Node(Red, Node(Black, l, k, v, a), ka, va, Node(Black, b, kb, vb, c))
    Node(_, a, ka, va, Node(Red, b, kb, vb, c)) -> Node(Red, Node(Black, l, k, v, a), ka, va, Node(Black, b, kb, vb, c))
    Node(_, a, ka, va, b) -> Node(Black, l, k, v, Node(Red, a, ka, va, b))
    Leaf -> Leaf

fun ins(t : tree, k : int, v : bool) : tree
  match t
    Leaf -> Node(Red, Leaf, k, v, Leaf)
    Node(Red, l, kx, vx, r) ->
      if k < kx then Node(Red, ins(l, k, v), kx, vx, r)
      elif k == kx then Node(Red, l, k, v, r)
      else Node(Red, l, kx, vx, ins(r, k, v))
    Node(Black, l, kx, vx, r) ->
      if k < kx then (if red(l) then balance-left(ins(l, k, v), kx, vx, r) else Node(Black, ins(l, k, v), kx, vx, r))
      elif k == kx then Node(Black, l, k, v, r)
      elif red(r) then balance-right(l, kx, vx, ins(r, k, v))
      else Node(Black, l, kx, vx, ins(r, k, v))

fun set-black(t : tree) : tree
  match t
    Node(_, l, k, v, r) -> Node(Black, l, k, v, r)
    Leaf -> Leaf

fun insert(t : tree, k : int, v : bool) : tree
  if red(t) then set-black(ins(t, k, v)) else ins(t, k, v)

fun fold(t : tree, acc : a, f : (int, bool, a) -> e a) : e a
  match t
    Node(_, l, k, v, r) -> fold(r, f(k, v, fold(l, acc, f)), f)
    Leaf -> acc

// The trees after every `every`th insertion, the last tree first.
fun make-trees(k : int, every : int, t : tree, trees : list<tree>) : div list<tree>
  if k <= 0 then Cons(t, trees)
  else
    val t' = insert(t, k, k % 10 == 0)
    make-trees(k - 1, every, t', if k % every == 0 then Cons(t', trees) else trees)

pub fun main()
  match make-trees(4200000, 5, Leaf, [])
    Cons(last) -> println(last.fold(0, fn(_, v, count) if v then count + 1 else count))
    Nil -> ()
