(* deriv: differentiates x^x ten times, simplifying each derivative as it is built, and prints the
   size of each (Reinking et al., Perceus, PLDI 2021). *)

type expr =
  | Val of int
  | Var of string
  | Add of expr * expr
  | Mul of expr * expr
  | Pow of expr * expr
  | Ln of expr

let pown a n =
  let rec go r i = if i <= 0 then r else go (r * a) (i - 1) in
  go 1 n

let rec add a b =
  match (a, b) with
  | Val n, Val m -> Val (n + m)
  | Val 0, f | f, Val 0 -> f
  | f, Val n -> add (Val n) f
  | Val n, Add (Val m, f) -> add (Val (n + m)) f
  | f, Add (Val n, g) -> add (Val n) (add f g)
  | Add (f, g), h -> add f (add g h)
  | f, g -> Add (f, g)

let rec mul a b =
  match (a, b) with
  | Val n, Val m -> Val (n * m)
  | Val 0, _ | _, Val 0 -> Val 0
  | Val 1, f | f, Val 1 -> f
  | f, Val n -> mul (Val n) f
  | Val n, Mul (Val m, f) -> mul (Val (n * m)) f
  | f, Mul (Val n, g) -> mul (Val n) (mul f g)
  | Mul (f, g), h -> mul f (mul g h)
  | f, g -> Mul (f, g)

let pow a b =
  match (a, b) with
  | Val m, Val n -> Val (pown m n)
  | _, Val 0 -> Val 1
  | f, Val 1 -> f
  | Val 0, _ -> Val 0
  | f, g -> Pow (f, g)

let ln = function Val 1 -> Val 0 | f -> Ln f

(* The derivative of an expression by [x]. *)
let rec d x = function
  | Val _ -> Val 0
  | Var y -> if String.equal x y then Val 1 else Val 0
  | Add (f, g) -> add (d x f) (d x g)
  | Mul (f, g) -> add (mul f (d x g)) (mul g (d x f))
  | Pow (f, g) ->
      mul (pow f g)
        (add (mul (mul g (d x f)) (pow f (Val (-1)))) (mul (ln f) (d x g)))
  | Ln f -> mul (d x f) (pow f (Val (-1)))

let rec count = function
  | Val _ | Var _ -> 1
  | Add (f, g) | Mul (f, g) | Pow (f, g) -> count f + count g
  | Ln f -> count f

let () =
  let x = Var "x" in
  let f = ref (pow x x) in
  for i = 1 to 10 do
    f := d "x" !f;
    Printf.printf "%d count: %d\n" i (count !f)
  done;
  print_endline "done"
