(* binary-trees: builds perfect binary trees bottom-up and counts their nodes, as the Benchmarks
   Game's program does, on one thread. *)

type tree = Leaf | Node of tree * tree

let rec make depth =
  if depth = 0 then Node (Leaf, Leaf)
  else Node (make (depth - 1), make (depth - 1))

let rec check = function Leaf -> 0 | Node (l, r) -> 1 + check l + check r

let () =
  let min_depth = 4 and max_depth = 16 in
  let stretch = max_depth + 1 in
  Printf.printf "stretch tree of depth %d\t check: %d\n" stretch
    (check (make stretch));
  let long_lived = make max_depth in
  let rec depths depth =
    if depth <= max_depth then begin
      let iterations = 1 lsl (max_depth - depth + min_depth) in
      let total = ref 0 in
      for _ = 1 to iterations do
        total := !total + check (make depth)
      done;
      Printf.printf "%d\t trees of depth %d\t check: %d\n" iterations depth
        !total;
      depths (depth + 2)
    end
  in
  depths min_depth;
  Printf.printf "long lived tree of depth %d\t check: %d\n" max_depth
    (check long_lived)
