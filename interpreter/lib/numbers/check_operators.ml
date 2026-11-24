(* Operators, and the types they are defined on (numbers.no-implicit-conversions and numbers.comparisons). *)

module T = Types
open Check_state
open Check_expect

let integer_name t =
  match T.numeric_name t with
  | Some name when List.mem name T.integer_types -> Some name
  | _ -> None

(* Whether a type supports an operator (numbers.no-implicit-conversions and numbers.comparisons), or [None]
   while the type is still open. *)
let supports ty rule =
  match (T.resolve ty, rule) with
  | Var _, _ -> None
  | Error, _ -> Some true
  | t, _ when t = T.never -> Some true
  | t, Numeric -> Some (Option.is_some (T.numeric_name t))
  | t, Integer -> Some (Option.is_some (integer_name t))
  | t, Negatable -> (
      match T.numeric_name t with
      | Some name -> Some (name.[0] <> 'u')
      | None -> Some false)
  | t, Bool_or_integer -> Some (t = T.bool || Option.is_some (integer_name t))

let unsupported st ty rule loc =
  let hint =
    if T.resolve ty = T.str && rule = Numeric then
      "; build strings with interpolation, as in \"{a}{b}\""
    else ""
  in
  error st Code.e0317 loc "this operator isn't defined on `%s`%s" (show ty) hint

(* The type of an operator's result, which is the type [ty] of its operands.
   An operator that [ty] doesn't support is an error, and its result then has
   the error type (errors.error-type). While [ty] is open, the check waits for the
   end of the body. *)
let operator st ty rule loc =
  match supports ty rule with
  | Some true -> ty
  | Some false ->
      unsupported st ty rule loc;
      T.Error
  | None ->
      st.operators <- (ty, rule, loc) :: st.operators;
      ty

let not_an_amount st ty loc =
  error st Code.e0311 loc
    "expected an integer type for the shift amount, found `%s`" (show ty)

(* A shift amount, checked with no expected type, must be an integer
   (numbers.shift-amounts). While its type is open, the check waits for the end of
   the body, where an open literal has its default type. *)
let amount ctx (b : Hir.expr) =
  let st = ctx.st in
  let y = infer ctx None b in
  (match supports y.ty Integer with
  | Some false -> not_an_amount st y.ty b.loc
  | None -> st.amounts <- (y.ty, b.loc) :: st.amounts
  | Some true -> ());
  y

(* The amount by which a place of type [ty] is shifted, or the value that a
   place of a type that no shift is defined on is assigned, checked alone. *)
let amount_of ctx ty b =
  if supports ty Integer = Some false then infer ctx None b else amount ctx b

(* A shift's result has the type of its left operand, which an amount of any
   integer type shifts (numbers.shifts). *)
let shift ctx loc op (x : Tast.expr) b =
  match supports x.ty Integer with
  | Some false ->
      unsupported ctx.st x.ty Integer loc;
      let y = infer ctx None b in
      node (Binary (op, x, y)) T.Error loc
  | Some true | None ->
      let y = amount ctx b in
      node (Binary (op, x, y)) (operator ctx.st x.ty Integer loc) loc

(* The operands of a binary operator have one type (numbers.no-implicit-conversions and numbers.comparisons),
   but for a shift's. A left operand of type [Never] converts to the right
   one's (declarations.never). Operands that disagree leave the result's type
   unknown. *)
let binary ctx loc (op : Ast.binary) a b =
  let st = ctx.st in
  let x = infer ctx None a in
  let operands () =
    if is_never x.ty then
      let y = infer ctx None b in
      (y, Some y.ty)
    else
      let y, same = check_fits ctx x.ty b in
      (y, if same then Some x.ty else None)
  in
  match op with
  | And | Or ->
      subsume st a.loc ~expected:T.bool x.ty;
      let y = check ctx T.bool b in
      node (Binary (op, x, y)) T.bool loc
  | Eq | Ne | Lt | Le | Gt | Ge ->
      let y, ty = operands () in
      let trait = match op with Eq | Ne -> "Eq" | _ -> "Ord" in
      Option.iter (fun ty -> obligation st ty (prelude_trait trait) loc) ty;
      node (Binary (op, x, y)) T.bool loc
  | Shl | Shr -> shift ctx loc op x b
  | Add | Sub | Mul | Div | Rem | Add_wrap | Sub_wrap | Mul_wrap | Bit_and
  | Bit_or | Bit_xor -> (
      let rule =
        match op with Add | Sub | Mul | Div | Rem -> Numeric | _ -> Integer
      in
      (* expressions.left-operand-first and expressions.right-operand: an operator that the left operand's known type
         doesn't support is the error, and the right operand is checked
         alone. *)
      match supports x.ty rule with
      | Some false ->
          unsupported st x.ty rule loc;
          let y = infer ctx None b in
          node (Binary (op, x, y)) T.Error loc
      | Some true | None ->
          let y, ty = operands () in
          let ty = Option.map (fun ty -> operator st ty rule loc) ty in
          node (Binary (op, x, y)) (Option.value ty ~default:T.Error) loc)
