(* The operators on numbers and booleans (numbers.no-implicit-conversions, numbers.comparisons and numbers.ieee-754). *)

open Value
open Eval_state
open Eval_types

let truth = function Bool b -> b | _ -> invalid_arg "Eval_operators.truth"

let int_operator : Ast.binary -> Ints.kind -> int64 -> int64 -> int64 = function
  | Add -> Ints.add
  | Sub -> Ints.sub
  | Mul -> Ints.mul
  | Div -> Ints.div
  | Rem -> Ints.rem
  | Add_wrap -> Ints.add_wrap
  | Sub_wrap -> Ints.sub_wrap
  | Mul_wrap -> Ints.mul_wrap
  | Bit_and -> fun _ -> Ints.logand
  | Bit_or -> fun _ -> Ints.logor
  | Bit_xor -> fun _ -> Ints.logxor
  | Shl | Shr | Eq | Ne | Lt | Le | Gt | Ge | And | Or ->
      invalid_arg "Eval_operators.int_operator"

let float_operator : Ast.binary -> float -> float -> float = function
  | Add -> ( +. )
  | Sub -> ( -. )
  | Mul -> ( *. )
  | Div -> ( /. )
  | Rem -> Float.rem
  | _ -> invalid_arg "Eval_operators.float_operator"

let arithmetic fr loc op ty a b =
  match (numeric ty, a, b) with
  | Integer k, Int x, Int y ->
      guard fr loc (fun () -> Int (int_operator op k x y))
  | Floating f32, Float x, Float y ->
      Float (Floats.result ~f32 (float_operator op x y))
  | _ -> invalid_arg "Eval_operators.arithmetic"

(* numbers.shift-amounts: a shift's amount has an integer type of its own. *)
let shift fr loc (op : Ast.binary) ty ~amount a b =
  let by =
    match numeric amount with
    | Integer by -> by
    | _ -> invalid_arg "Eval_operators.shift"
  in
  match (numeric ty, op, a, b) with
  | Integer k, Shl, Int x, Int n ->
      guard fr loc (fun () -> Int (Ints.shift_left k ~by x n))
  | Integer k, Shr, Int x, Int n ->
      guard fr loc (fun () -> Int (Ints.shift_right k ~by x n))
  | _ -> invalid_arg "Eval_operators.shift"

let unary fr loc (op : Ast.unary) ty v =
  match (op, numeric ty, v) with
  | Not, _, Bool b -> Bool (not b)
  | Not, Integer k, Int x -> Int (Ints.lognot k x)
  | Neg, Integer k, Int x -> guard fr loc (fun () -> Int (Ints.neg k x))
  | Neg, _, Float x -> Float (-.x)
  | _ -> invalid_arg "Eval_operators.unary"
