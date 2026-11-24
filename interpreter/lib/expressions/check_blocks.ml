(* Blocks, and the statements in them: bindings and assignments. *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_types
open Check_fields
open Check_patterns
open Check_refutable
open Check_operators

(* expressions.option-fallback: the [Option] fallback [a else b], once [a] is inferred as
   [x]. *)
let option_fallback ctx loc (a : Hir.expr) (x : A.expr) b =
  let st = ctx.st in
  let inner =
    match T.resolve x.ty with
    | Error -> T.Error
    | _ ->
        let inner = fresh st a.loc in
        if fits st a.loc ~expected:(T.option inner) x.ty then inner else T.Error
  in
  let y = check ctx inner b in
  node (Else (x, y)) inner loc

let let_else ctx written annotation (p : Hir.pattern) v otherwise : A.binding =
  let st = ctx.st in
  let pat = pattern ctx p (Option.value annotation ~default:v.A.ty) in
  let o = infer ctx None otherwise in
  if not (is_never o.ty || T.resolve o.ty = Error) then
    error st Code.e0311 otherwise.loc
      "the `else` branch of a let-else must have type `Never`, not `%s`"
      (show o.ty);
  { pattern = pat; written; value = v; otherwise = Some o }

(* A binding without let-else, whose pattern must be irrefutable once checked
   (patterns.irrefutable-positions). *)
let plain ctx written annotation (p : Hir.pattern) (v : A.expr) : A.binding =
  let pat = pattern ctx p (Option.value annotation ~default:v.ty) in
  require_irrefutable ctx.st p;
  { pattern = pat; written; value = v; otherwise = None }

(* patterns.let-else: a binding whose value is an [else] is a let-else when its
   pattern is refutable, its names written without a module read against the
   annotation's type, or else the type of the expression before [else] (patterns.variants-by-type), and otherwise the [Option] fallback. *)
let binding ctx ({ pattern = p; annotation; value } : Hir.binding) : A.binding =
  let st = ctx.st in
  let written = annotation in
  let annotation = Option.map (of_hir st) annotation in
  match value.desc with
  | Else (source, otherwise) -> (
      let inferred, against =
        match annotation with
        | Some t -> (None, t)
        | None ->
            let x = infer ctx None source in
            (Some x, x.ty)
      in
      let checked e =
        match inferred with
        | Some x -> x
        | None -> infer_checked ctx annotation e
      in
      match irrefutable st ~ty:against p with
      | false -> let_else ctx written annotation p (checked source) otherwise
      | true ->
          let v =
            match inferred with
            | Some x -> option_fallback ctx value.loc source x otherwise
            | None -> infer_checked ctx annotation value
          in
          plain ctx written annotation p v)
  | _ -> plain ctx written annotation p (infer_checked ctx annotation value)

let assignment ctx (op : Ast.binary option) place value : A.stmt_desc =
  let st = ctx.st in
  let p = infer ctx None place in
  (* What isn't a place has no type that the value must fit (errors.error-type). *)
  let p =
    if not (checked_place place p) then (
      error st Code.e0401 place.loc
        "only a variable, a field, an element or a projection's call can be \
         assigned to";
      { p with ty = T.Error })
    else if through_option p then (
      error st Code.e0401 place.loc
        "a field read through an `Option` is a copy, so it can't be assigned to";
      { p with ty = T.Error })
    else p
  in
  let v =
    match op with
    | Some (Shl | Shr) -> amount_of ctx p.ty value
    | _ -> check ctx p.ty value
  in
  (match op with
  | None -> ()
  | Some (Add | Sub | Mul | Div | Rem) ->
      ignore (operator st p.ty Numeric place.loc)
  | Some _ -> ignore (operator st p.ty Integer place.loc));
  Assign (op, p, v)

(* projections.yield: [yield e] hands the caller a place of the projection's
   type, or a view that a temporary holds. *)
let yield_stmt ctx loc (operand : Hir.expr) : A.stmt_desc =
  let st = ctx.st in
  match ctx.yields with
  | None ->
      error st Code.e0425 loc
        "`yield` belongs in a projection's body, a function whose result is \
         written `inout T`";
      Yield (abandon ctx operand)
  | Some ty ->
      let v = infer ctx (Some ty) operand in
      if checked_place operand v && not (through_option v) then (
        (* A place is handed to the caller, so its type is the result's
           exactly. *)
        expect st operand.loc ~expected:ty v.ty;
        Yield v)
      else if Views_types.is_view v.ty then Yield v
      else (
        error st Code.e0401 operand.loc
          "only a variable, a field, an element or a projection's call can be \
           yielded";
        Yield { v with ty = T.Error })

(* handlers.resuming: a body that resumes may go on, dropping what the rest of
   the block gave, so a [resume] needs no [let _ =] as a statement. *)
let resumes (e : Hir.expr) = match e.desc with Resume _ -> true | _ -> false

(* A block and its type. Checked against an expected type, a block has that
   type: its final expression is checked against it, and a block without one
   has type [()], which must fit it, as reported at [at]. *)
let block_expr ctx ~at expected (stmts : Hir.block) : A.block * T.ty =
  let st = ctx.st in
  let rec go acc = function
    | [] ->
        Option.iter (fun t -> subsume st at ~expected:t T.unit) expected;
        (List.rev acc, Option.value expected ~default:T.unit)
    | [ ({ desc = Expr e; _ } : Hir.stmt) ] ->
        let v = infer_checked ctx expected e in
        ( List.rev ({ A.stmt = Expr v; at = e.loc } :: acc),
          Option.value expected ~default:v.ty )
    | (s : Hir.stmt) :: rest ->
        let stmt =
          match s.desc with
          | Expr e ->
              let v = infer ctx None e in
              (* expressions.unused-values *)
              if not (resumes e) then
                st.units <- (v.ty, Statement, s.loc) :: st.units;
              A.Expr v
          | Let b -> Let (binding ctx b)
          | Var b -> Var (binding ctx b)
          | Assign (op, place, value) -> assignment ctx op place value
          | Assert e -> Assert (check ctx T.bool e)
          | Yield e -> yield_stmt ctx s.loc e
        in
        go ({ A.stmt; at = s.loc } :: acc) rest
  in
  go [] stmts

(* A loop's body, whose value is discarded, so that its last expression
   statement, like every other, must have type [()] or [Never] (expressions.statements). *)
let loop_body ctx ~at body =
  let b, ty = block_expr ctx ~at None body in
  (match List.rev body with
  | { desc = Expr e; loc } :: _ when not (resumes e) ->
      ctx.st.units <- (ty, Statement, loc) :: ctx.st.units
  | _ -> ());
  b
