(* cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its constants,
   then evaluates it before and after (Reinking et al., Perceus, PLDI 2021). *)

type expr = Var of int | Val of int | Add of expr * expr | Mul of expr * expr

let rec make n v =
  if n = 0 then if v = 0 then Var 1 else Val v
  else Add (make (n - 1) (v + 1), make (n - 1) (Int.max (v - 1) 0))

let rec append_add a b =
  match a with Add (x, y) -> Add (x, append_add y b) | _ -> Add (a, b)

let rec append_mul a b =
  match a with Mul (x, y) -> Mul (x, append_mul y b) | _ -> Mul (a, b)

let rec reassoc = function
  | Add (a, b) -> append_add (reassoc a) (reassoc b)
  | Mul (a, b) -> append_mul (reassoc a) (reassoc b)
  | e -> e

let rec fold = function
  | Add (a, b) -> (
      match (fold a, fold b) with
      | Val x, Val y -> Val (x + y)
      | Val x, Add (f, Val y) | Val x, Add (Val y, f) -> Add (Val (x + y), f)
      | a, b -> Add (a, b))
  | Mul (a, b) -> (
      match (fold a, fold b) with
      | Val x, Val y -> Val (x * y)
      | Val x, Mul (f, Val y) | Val x, Mul (Val y, f) -> Mul (Val (x * y), f)
      | a, b -> Mul (a, b))
  | e -> e

let rec eval = function
  | Var _ -> 0
  | Val v -> v
  | Add (a, b) -> eval a + eval b
  | Mul (a, b) -> eval a * eval b

let () =
  let e = make 20 1 in
  Printf.printf "%d\n" (eval e);
  Printf.printf "%d\n" (eval (fold (reassoc e)))
