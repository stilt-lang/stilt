(* The operations that can overflow (numbers.integer-panics and numbers.shifts; effects.overflow-effect): integer [+], [-] and [*], their compound assignments, [-] on a value
   that isn't a literal, [/] and [%] on a signed type unless the divisor is a
   literal other than [-1], and a shift unless its amount is a literal below
   the left operand's width. Wrapping operators can't. A call of [div_euclid]
   or [rem_euclid] by a literal names no native (std.integers), so its
   overflow by [-1] is its own. *)

open Tast

(* The value of an integer literal, [-] before one included, when it fits in
   an [int]. The canonical text of zero is empty. *)
let literal (e : expr) =
  let value text =
    match Literal.int_canonical text with
    | "" -> Some 0
    | canonical -> int_of_string_opt canonical
  in
  match e.desc with
  | Int text -> value text
  | Unary (Neg, { desc = Int text; _ }) -> Option.map Int.neg (value text)
  | _ -> None

let kind ty = Option.bind (Check_operators.integer_name ty) Ints.of_name

(* The operator as messages name it, if [op] on [left]'s type, with [right]
   its second operand, can overflow. *)
let binary (op : Ast.binary) left (right : expr) =
  match kind left with
  | None -> None
  | Some { bits; signed } -> (
      let not_literal p = Option.fold ~none:true ~some:p (literal right) in
      match op with
      | Add -> Some "`+`"
      | Sub -> Some "`-`"
      | Mul -> Some "`*`"
      | Div when signed && not_literal (fun v -> v = -1) -> Some "`/`"
      | Rem when signed && not_literal (fun v -> v = -1) -> Some "`%`"
      | Shl when not_literal (fun v -> v < 0 || v >= bits) -> Some "`<<`"
      | Shr when not_literal (fun v -> v < 0 || v >= bits) -> Some "`>>`"
      | _ -> None)

(* What can overflow and where, as [(this `+` can overflow, loc)]. *)
let site what loc = (Printf.sprintf "this %s can overflow" what, loc)

(* The overflow of a compound assignment, as [s += x], if it can. *)
let stmt (s : stmt) =
  match s.stmt with
  | Assign (Some op, p, v) -> (
      match binary op p.ty v with
      | Some what ->
          let what = String.sub what 0 (String.length what - 1) ^ "=`" in
          [ site what s.at ]
      | None -> [])
  | _ -> []

(* The overflow of an operator, as [a + b] or [-a]. *)
let expr (e : expr) =
  match e.desc with
  | Binary (op, a, b) -> (
      match binary op a.ty b with
      | Some what -> [ site what e.loc ]
      | None -> [])
  | Unary (Neg, a)
    when literal e = None
         && Option.fold ~none:false
              ~some:(fun (k : Ints.kind) -> k.signed)
              (kind a.ty) ->
      [ site "`-`" e.loc ]
  | Call (Member (_, (("div_euclid" | "rem_euclid") as name)), _, [ a; b ], _)
    when Option.fold ~none:false
           ~some:(fun (k : Ints.kind) -> k.signed)
           (kind a.value.ty)
         && literal b.value = Some (-1) ->
      [ site (Printf.sprintf "`%s` by `-1`" name) e.loc ]
  | _ -> []
