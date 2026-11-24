(* rbtree-ck: rbtree, keeping a list of every fifth tree it makes, which share most of their nodes,
   and folding over the last to count its true values (Reinking et al., Perceus, PLDI 2021). *)

type color = Red | Black
type tree = Leaf | Node of color * tree * int * bool * tree

let is_red = function Node (Red, _, _, _, _) -> true | _ -> false

(* Rebalances a black node whose left child [l] is red. *)
let balance_left l k v r =
  match l with
  | Node (_, Node (Red, a, ka, va, b), kb, vb, c)
  | Node (_, a, ka, va, Node (Red, b, kb, vb, c)) ->
      Node (Red, Node (Black, a, ka, va, b), kb, vb, Node (Black, c, k, v, r))
  | Node (_, a, ka, va, b) -> Node (Black, Node (Red, a, ka, va, b), k, v, r)
  | Leaf -> Leaf

(* Rebalances a black node whose right child [r] is red. *)
let balance_right l k v r =
  match r with
  | Node (_, Node (Red, a, ka, va, b), kb, vb, c)
  | Node (_, a, ka, va, Node (Red, b, kb, vb, c)) ->
      Node (Red, Node (Black, l, k, v, a), ka, va, Node (Black, b, kb, vb, c))
  | Node (_, a, ka, va, b) -> Node (Black, l, k, v, Node (Red, a, ka, va, b))
  | Leaf -> Leaf

let rec ins t k v =
  match t with
  | Leaf -> Node (Red, Leaf, k, v, Leaf)
  | Node (Red, l, kx, vx, r) ->
      if k < kx then Node (Red, ins l k v, kx, vx, r)
      else if k = kx then Node (Red, l, k, v, r)
      else Node (Red, l, kx, vx, ins r k v)
  | Node (Black, l, kx, vx, r) ->
      if k < kx then
        if is_red l then balance_left (ins l k v) kx vx r
        else Node (Black, ins l k v, kx, vx, r)
      else if k = kx then Node (Black, l, k, v, r)
      else if is_red r then balance_right l kx vx (ins r k v)
      else Node (Black, l, kx, vx, ins r k v)

let set_black = function
  | Node (_, l, k, v, r) -> Node (Black, l, k, v, r)
  | Leaf -> Leaf

let insert t k v = if is_red t then set_black (ins t k v) else ins t k v

let rec fold f t acc =
  match t with
  | Leaf -> acc
  | Node (_, l, k, v, r) -> fold f r (f k v (fold f l acc))

(* The trees after every [every]th insertion, the last tree first. *)
let make_trees n every =
  let rec go k t trees =
    if k <= 0 then t :: trees
    else
      let t = insert t k (k mod 10 = 0) in
      go (k - 1) t (if k mod every = 0 then t :: trees else trees)
  in
  go n Leaf []

let () =
  match make_trees 4_200_000 5 with
  | last :: _ ->
      Printf.printf "%d\n"
        (fold (fun _ v count -> if v then count + 1 else count) last 0)
  | [] -> ()
