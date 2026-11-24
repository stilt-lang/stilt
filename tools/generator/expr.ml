(* Expressions. Each is made for the type its context expects: a variable, a
   field or a call that has the type, or one of the forms that make a value of
   the type out of others. The modules of those forms take [expr] to make their
   operands. *)

open Code
open Context
open Ty

(* The functions that an expression can call to get a [ty]. A call that takes
   [inout] arguments is a statement of its own, so that no modification
   starts while an expression is reading (modes.overlap). *)
let callable b sc ty =
  List.filter
    (fun f ->
      f.ret = ty
      && List.for_all (fun (inout, _) -> not inout) f.params
      && affordable b sc f.cost)
    b.p.fns

(* The fields of variables in scope that have type [ty], as [v.f] or [v.0]. *)
let fields_of b sc ty =
  List.concat_map
    (fun v ->
      match v.ty with
      | Named name -> (
          match decl b name with
          | Record fields ->
              List.filter_map
                (fun (f, t) -> if t = ty then Some (v.name ^ "." ^ f) else None)
                fields
          | Variants _ -> [])
      | Tuple ts ->
          List.concat
            (List.mapi
               (fun i t ->
                 if t = ty then [ v.name ^ "." ^ string_of_int i ] else [])
               ts)
      | _ -> [])
    sc.vars

(* [c] in a block that fixes its type: [{ let k: T = c; k }]. *)
let annotated b ty c =
  let k = fresh b.p "k" in
  compound (Printf.sprintf "{ let %s: %s = %s; %s }" k (to_string ty) c.text k)

(* An expression of type [ty]. With [~known:true], its type is fixed without
   an expected type. *)
let rec expr b sc ~depth ~known ty =
  let r = b.p.r in
  let vars = typed sc.vars ty in
  let fields = fields_of b sc ty in
  let calls = if depth > 0 then callable b sc ty else [] in
  let deeper = if depth > 0 then by_type b sc ~depth ~known ty else [] in
  let c =
    Pick.run r
      ([
         ((if vars = [] then 0 else 8), fun () -> atom (Pick.one r vars).name);
         ((if fields = [] then 0 else 3), fun () -> atom (Pick.one r fields));
         (3, fun () -> Values.value expr b sc ~depth ~known ty);
         ( (if calls = [] then 0 else 3),
           fun () -> call b sc ~depth (Pick.one r calls) );
       ]
      @ deeper)
  in
  if known && not c.known then annotated b ty c else c

(* A call of [f], marked as effects.marking requires. Where a raise can't escape, the
   call is caught. *)
and call b sc ~depth f =
  spend b sc f.cost;
  let args =
    List.map
      (fun (_, t) -> (expr b sc ~depth:(depth - 1) ~known:false t).text)
      f.params
  in
  let text = call_text f.fname args in
  if not f.raises then atom text
  else if sc.may_raise then compound ("try " ^ text)
  else compound ("try " ^ text ^ " catch " ^ handler b sc ~depth f.ret)

(* The arms of a [catch] of [Fault] whose bodies have type [ty]: a catch-all,
   which needs a reason (effects.catch-alls-need-reason), or an arm for each variant. *)
and handler b sc ~depth ty =
  let r = b.p.r in
  let d = depth - 1 in
  if Pick.chance r 0.6 then
    Printf.sprintf "_ because \"%s\" => %s" (Lit.string_body r)
      (expr b sc ~depth:d ~known:false ty).text
  else
    let arm (case, payload) =
      let bound =
        List.map
          (fun t -> { name = fresh b.p "e"; ty = t; mutable_ = false })
          payload
      in
      let pattern =
        if bound = [] then case
        else call_text case (List.map (fun v -> v.name) bound)
      in
      let sc = { sc with vars = bound @ sc.vars } in
      pattern ^ " => " ^ (expr b sc ~depth:d ~known:false ty).text
    in
    "{ " ^ String.concat ", " (List.map arm b.p.fault_variants) ^ " }"

(* The forms that make a [ty] out of other values. *)
and by_type b sc ~depth ~known ty =
  let d = depth - 1 in
  let common =
    [
      (1, fun () -> if_expr b sc ~depth ~known ty);
      (1, fun () -> Patterns.match_expr expr b sc ~depth ~known ty);
      ( 2,
        fun () ->
          let o = expr b sc ~depth:d ~known (Option ty) in
          let fallback = expr b sc ~depth:d ~known:false ty in
          compound ~known:o.known (operand o ^ " else " ^ operand fallback) );
      (1, fun () -> Closures.fold expr b sc ~depth ty);
    ]
  in
  let specific =
    match ty with
    | Int k -> Numbers.int_ops expr b sc ~depth ~known k
    | Float k -> Numbers.float_ops expr b sc ~depth ~known k
    | Bool -> Bools.bool_ops expr b sc ~depth
    | Str -> Texts.str_ops expr b sc ~depth
    | List t -> Lists.list_ops expr b sc ~depth t
    | Option t -> Options.option_ops expr b sc ~depth t
    | Unit | Tuple _ | Map _ | Named _ -> []
  in
  common @ specific

and cond b sc ~depth = Bools.cond expr b sc ~depth

and if_expr b sc ~depth ~known ty =
  let d = depth - 1 in
  let c = cond b sc ~depth:d in
  let x = expr b sc ~depth:d ~known ty in
  let y = expr b sc ~depth:d ~known:false ty in
  compound ~known:x.known
    (Printf.sprintf "if %s { %s } else { %s }" (head c.text) x.text y.text)

(* The forms that statements use too, made with [expr]. *)

let closure b sc ~depth ?known param ty =
  Closures.closure expr b sc ~depth ?known param ty

let interpolation b sc ~depth = Texts.interpolation expr b sc ~depth
let scrutinee b sc ~depth = Patterns.scrutinee expr b sc ~depth
