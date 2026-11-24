(* binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree
   of depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
   Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021). *)

type tree = Tip | Node of tree * tree

let rec make depth =
  if depth > 0 then Node (make (depth - 1), make (depth - 1))
  else Node (Tip, Tip)

let rec check = function Node (l, r) -> check l + check r + 1 | Tip -> 0

let () =
  let min_depth = 4 and max_depth = 21 in
  let stretch = max_depth + 1 in
  Printf.printf "stretch tree of depth %d\t check: %d\n" stretch
    (check (make stretch));
  let long_lived = make max_depth in
  let rec depths depth =
    if depth <= max_depth then begin
      let count = 1 lsl (max_depth + min_depth - depth) in
      let total = ref 0 in
      for _ = 1 to count do
        total := !total + check (make depth)
      done;
      Printf.printf "%d\t trees of depth %d\t check: %d\n" count depth !total;
      depths (depth + 2)
    end
  in
  depths min_depth;
  Printf.printf "long lived tree of depth %d\t check: %d\n" max_depth
    (check long_lived)
