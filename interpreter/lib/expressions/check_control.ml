(* Branches and loops: [if], [if let], [match], [try … catch], [loop], [while] and
   [for]. *)

module T = Types
module A = Tast
open Check_state
open Check_unify
open Check_expect
open Check_effects
open Check_patterns
open Check_refutable
open Check_operators
open Check_blocks

(* Whether a loop's body holds a [break] that exits it, outside any nested
   loop or closure (expressions.break-and-continue). *)
let rec breaks (e : Hir.expr) =
  match e.desc with
  | Break -> true
  | Loop _ | Closure _ -> false
  (* The head of a [while] and the iterable of a [for] are outside its
     body. *)
  | While (cond, _) -> breaks cond
  | For (_, Iter source, _) -> breaks source
  | For (_, Range (a, b, _), _) -> breaks a || breaks b
  | Block b -> breaks_block b
  | If (c, b, alt) | If_let (_, c, b, alt) ->
      breaks c || breaks_block b || Option.fold ~none:false ~some:breaks alt
  | Match (s, arms) -> breaks s || List.exists breaks_arm arms
  | Try (e, arms) ->
      breaks e || Option.fold ~none:false ~some:(List.exists breaks_arm) arms
  | Field (e, _) | Unary (_, e) | Raise e -> breaks e
  | Return e -> Option.fold ~none:false ~some:breaks e
  | Call (f, args) ->
      breaks f || List.exists (fun (a : Hir.arg) -> breaks a.value) args
  | Index (a, b) | Binary (_, a, b) | Else (a, b) -> breaks a || breaks b
  | Tuple es | List es -> List.exists breaks es
  | Struct (_, base, fields) | Record_literal (base, fields) ->
      Option.fold ~none:false ~some:breaks base
      || List.exists (fun (f : Hir.field_init) -> breaks f.value) fields
  | Spread e -> breaks e
  | Interpolated segments ->
      List.exists
        (function Hir.Splice (e, _) -> breaks e | Text _ -> false)
        segments
  | With (handlers, b) -> List.exists breaks handlers || breaks_block b
  | Resume e -> Option.fold ~none:false ~some:breaks e
  | When (_, b) | Unsafe b -> breaks_block b
  | Comptime e -> breaks e
  (* macros.outside-run: a quote's splices are evaluated where it is. *)
  | Quote q -> List.exists (fun (s : Hir.splice) -> breaks s.value) q.splices
  | Int _ | Float _ | Str _ | Bool _ | Local _ | Func _ | Const _ | Variant _
  | Member _ | Key_root | Hole | Continue | Error | Perform _ | Handler _
  | Value_param _ | Bound_test _ ->
      false

and breaks_arm (a : Hir.arm) =
  Option.fold ~none:false ~some:breaks a.guard || breaks a.body

and breaks_block b =
  List.exists
    (fun (s : Hir.stmt) ->
      match s.desc with
      | Let b | Var b -> breaks b.value
      | Assign (_, p, v) -> breaks p || breaks v
      | Assert e | Yield e | Expr e -> breaks e)
    b

(* Only a [catch] arm can give a reason, and the grammar gives it no guard
   then. *)
let arm ctx expected scrutinee (a : Hir.arm) : A.arm =
  let st = ctx.st in
  let mark = Meta.mark () in
  let p = pattern ctx a.pattern scrutinee in
  let guard = Option.map (check ctx T.bool) a.guard in
  (* effects.catch-alls-need-reason and effects.reasons-only-on-catch-alls *)
  (match (a.because, a.pattern.desc) with
  | Some _, (P_wild | P_bind _ | P_error) | None, _ -> ()
  | Some _, P_bare _
    when Hashtbl.find_opt st.bare a.pattern.loc = Some Named_error ->
      ()
  | Some reason, _ ->
      error st Code.e0504 reason.loc
        "only a catch-all arm gives a reason with `because`");
  let body = infer_checked ctx expected a.body in
  (* meta.fresh-types: an arm whose value decides the form's type. *)
  let body =
    if expected = None then Check_fresh.arm_value st mark body else body
  in
  { pattern = p; guard; because = Option.is_some a.because; body }

(* The branches of an [if] or an [if let], whose condition [desc] makes the
   node from its checked branches (expressions.if-let). [within] checks the
   first branch, which a bound test's bounds hold in (meta.bound-tests), and
   whose value may not hold a fresh type that its pattern made after [mark]
   (meta.fresh-types). *)
let branches ?(within = fun k -> k ()) ?mark ctx expected loc body alt desc =
  let st = ctx.st in
  let at b alt ty = node (desc b alt) ty loc in
  let first expected =
    let b, ty = within (fun () -> block_expr ctx ~at:loc expected body) in
    match (mark, expected) with
    | Some m, None ->
        let checked = Check_fresh.arm_value st m (node (Block b) ty loc) in
        (b, checked.ty)
    | _ -> (b, ty)
  in
  match alt with
  | None ->
      let b, ty = first None in
      (* A block whose type is still unknown decides the [if]'s at the
         end of the body, and a block with a value has an error there, so
         the [if] reports one error or the other. *)
      let if_ty =
        match (T.resolve ty, T.unsolved ty) with
        | Var _, Some { kind = Any; _ } -> fresh st loc
        | (Tuple [] | Error), _ -> T.unit
        | t, _ when t = T.never -> T.unit
        | _ -> T.Error
      in
      st.units <- (ty, If_without_else if_ty, loc) :: st.units;
      at b None if_ty
  | Some alt -> (
      let b, ty = first expected in
      match (expected, settled st ty loc) with
      | Some t, _ -> at b (Some (check ctx t alt)) t
      | None, Some common -> at b (Some (check ctx common alt)) common
      | None, None ->
          let a = infer ctx None alt in
          at b (Some a) a.ty)

let if_expr ctx expected loc (cond : Hir.expr) body alt =
  match cond.desc with
  (* meta.bound-tests: the branch that a bound test guards knows the bounds,
     and the [else] branch nothing more. *)
  | Bound_test (v, bounds) ->
      let bounds = Check_meta.tested v bounds in
      let c = node (Reflect (Implements (T.Param v, bounds))) T.bool cond.loc in
      branches ~within:(Check_meta.within ctx.st v bounds)
        ctx expected loc body alt (fun b alt -> A.If (c, b, alt))
  | _ ->
      let c = check ctx T.bool cond in
      branches ctx expected loc body alt (fun b alt -> A.If (c, b, alt))

(* The scrutinee is matched as a [match] arm would be (patterns.match). *)
let if_let_expr ctx expected loc p scrutinee body alt =
  let s = infer ctx None scrutinee in
  let mark = Meta.mark () in
  let p = pattern ctx p s.ty in
  branches ~mark ctx expected loc body alt (fun b alt ->
      A.If_let (p, s, b, alt))

let match_expr ctx expected loc scrutinee arms =
  let st = ctx.st in
  let s = infer ctx None scrutinee in
  let checked, common =
    List.fold_left
      (fun (checked, common) (a : Hir.arm) ->
        match (expected, common) with
        | Some _, _ -> (arm ctx expected s.ty a :: checked, common)
        | None, Some _ -> (arm ctx common s.ty a :: checked, common)
        | None, None ->
            let a = arm ctx None s.ty a in
            (a :: checked, settled st a.body.ty a.body.loc))
      ([], None) arms
  in
  let ty =
    match (expected, common) with
    | Some t, _ | None, Some t -> t
    | None, None -> T.never
  in
  node (Match (s, List.rev checked)) ty loc

(* effects.catch: the error type that the arms of a [catch] handle. The arms
   handle the operand's raise, and every other effect of the operand passes
   through, including those its open rows gain later. The error type is the
   first raise's, the error type where the operand holds an expression of the
   error type, which may raise it (errors.error-type-raises), or a variable while an
   open row may still raise. *)
let caught_type st loc x operand_rows =
  match
    List.find_map (fun (row, _) -> (T.row_contents row).raise) operand_rows
  with
  | Some t -> t
  | None when Walk.exists (fun (e : Tast.expr) -> T.resolve e.ty = T.Error) x ->
      T.Error
  | None when List.exists (fun (row, _) -> T.is_open row) operand_rows ->
      let v = fresh st loc in
      st.catch_errors <- v :: st.catch_errors;
      v
  | None -> T.never

let try_expr ctx expected loc operand arms =
  let st = ctx.st in
  let inner = { ctx with effects = ref [] } in
  let x, fitted =
    match expected with
    | Some t -> check_fits inner t operand
    | None -> (infer inner None operand, true)
  in
  match arms with
  | None ->
      ctx.effects := !(inner.effects) @ !(ctx.effects);
      (* An operand that doesn't fit the expected type has been reported, so
         the [try] has the error type rather than reporting it again. *)
      node (Try (x, None)) (if fitted then x.ty else T.Error) loc
  | Some arms ->
      let operand_rows = List.rev !(inner.effects) in
      let error_ty = caught_type st loc x operand_rows in
      let passed = T.fresh_row () in
      let report = reporter st in
      List.iter
        (fun (row, at) ->
          report at (fit ~handled:(Raise_of error_ty) row passed))
        operand_rows;
      perform ctx passed loc;
      let checked, common =
        List.fold_left
          (fun (checked, common) (a : Hir.arm) ->
            match (expected, common) with
            | Some _, _ -> (arm ctx expected error_ty a :: checked, common)
            | None, Some _ -> (arm ctx common error_ty a :: checked, common)
            | None, None ->
                let a = arm ctx None error_ty a in
                (a :: checked, settled st a.body.ty a.body.loc))
          ([], if expected = None then settled st x.ty operand.loc else None)
          arms
      in
      let ty =
        match (expected, common) with
        | Some t, _ | None, Some t -> t
        | None, None -> T.never
      in
      node (Try (x, Some { error = error_ty; arms = List.rev checked })) ty loc

let loop_expr ctx loc body =
  let b = loop_body ctx ~at:loc body in
  node (Loop b) (if breaks_block body then T.unit else T.never) loc

let while_expr ctx loc cond body =
  let c = check ctx T.bool cond in
  let b = loop_body ctx ~at:loc body in
  node (While (c, b)) T.unit loc

let list_element ty =
  match T.resolve ty with
  | Con (item, [ t ]) when item = T.prelude_item "List" -> Some t
  | _ -> None

let for_expr ctx loc target (iterable : Hir.iterable) body =
  let st = ctx.st in
  let it, elem =
    match iterable with
    | Iter source -> (
        let s = infer ctx None source in
        match known st source.loc s.ty with
        | Some (Con (item, [ t ])) when item = T.prelude_item "List" ->
            (A.Iter s, t)
        | Some (Con (item, [ k; v ])) when item = T.prelude_item "Map" ->
            (A.Iter s, T.Tuple [ k; v ])
        (* views.for-over-view: a view of a list, and an iterator. *)
        | Some (Con ({ home = "std.view"; name = "View" }, [ list ]))
          when Option.is_some (list_element list) ->
            (A.Iter s, Option.get (list_element list))
        | Some (Con ({ home = "std.view"; name = "Iter" }, [ t ])) ->
            (A.Iter s, t)
        (* meta.fields and meta.variant-cases: the fields or the cases of a type. *)
        | Some t when Option.is_some (Check_meta.element t) ->
            (A.Iter s, Option.get (Check_meta.element t))
        (* generics.array-iteration: an array yields its elements. *)
        | Some t when Option.is_some (Check_arrays.parts t) ->
            (A.Iter s, fst (Option.get (Check_arrays.parts t)))
        (* variadics.pack-tuples *)
        | Some t when Packs.has_spread t ->
            error st Code.e0342 source.loc
              "`%s` has as many elements as its pack, which this body doesn't \
               know, so `for` can't take it apart; map over it with a spread, \
               as `[..e]`"
              (show t);
            (A.Iter s, T.Error)
        | Some t ->
            error st Code.e0311 source.loc
              "expected a list, a map, a range, an array, a view of a list or \
               an iterator, found `%s`"
              (show t);
            (A.Iter s, T.Error)
        | None -> (A.Iter s, T.Error))
    | Range (a, b, kind) ->
        let x = infer ctx None a in
        let y = check ctx x.ty b in
        (A.Range (x, y, kind), operator st x.ty Integer a.loc)
  in
  let p = pattern ctx target elem in
  require_irrefutable st target;
  let b = loop_body ctx ~at:loc body in
  node (For (p, it, b)) T.unit loc
