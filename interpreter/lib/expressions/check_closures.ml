(* Closures, and key paths, which stand for closures (expressions.key-paths). *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_effects
open Check_types
open Check_patterns
open Check_refutable

let rec key_path (e : Hir.expr) =
  match e.desc with
  | Key_root -> true
  | Field (base, _) | Index (base, _) -> key_path base
  | Call (callee, _) -> key_path callee
  | _ -> false

(* expressions.key-paths: [.chain] means [|x| x.chain] where a function type of one
   parameter is expected. The arguments and indexes in the chain are
   expressions of their own, where a key path starts afresh. *)
let key_path_closure ctx expected (e : Hir.expr) =
  let st = ctx.st in
  match Option.map T.resolve expected with
  | Some (Fn ([ (Let, param) ], ret, row)) ->
      let v = Env.synthetic "it" in
      Hashtbl.replace st.locals v.id param;
      let rec rebase (e : Hir.expr) : Hir.expr =
        match e.desc with
        | Key_root -> { e with desc = Local v }
        | Field (base, field) -> { e with desc = Field (rebase base, field) }
        | Index (base, index) -> { e with desc = Index (rebase base, index) }
        | Call (callee, args) -> { e with desc = Call (rebase callee, args) }
        | _ -> e
      in
      let inner =
        { ctx with ret; yields = None; effects = ref []; known = [] }
      in
      let body = check inner ret (rebase e) in
      settle st !(inner.effects) row;
      let p : A.pattern = { pat = P_bind v; pty = param; ploc = e.loc } in
      node
        (Closure ([ p ], [], body))
        (T.Fn ([ (by_value, param) ], ret, row))
        e.loc
  | Some Error -> error_node e.loc
  | _ ->
      error st Code.e0324 e.loc
        "a key path is allowed only where a function type is expected";
      error_node e.loc

(* A closure's parameter, whose type is [expected_ty] where the closure's
   type is expected. *)
let closure_param ctx (p : Hir.closure_param) expected_ty =
  let st = ctx.st in
  let ty =
    match (p.annotation, expected_ty) with
    | Some a, Some t ->
        (* A parameter whose annotation contradicts its expected type
           has the error type. *)
        let a = of_hir st a in
        if agrees st p.pattern.loc ~expected:t a then a else T.Error
    | Some a, None -> of_hir st a
    | None, Some t -> t
    | None, None -> fresh st p.pattern.loc
  in
  let checked = pattern ctx p.pattern ty in
  require_irrefutable st p.pattern;
  checked

(* variadics.pack-inference: a closure where a function type whose parameters spread a
   pack not yet known is expected gives the pack one element for each of its
   parameters. *)
let fit_arity st loc (params : Hir.closure_param list) expected =
  match T.resolve expected with
  | Fn (ps, ret, row) when List.exists (fun (_, t) -> Packs.is_spread t) ps ->
      let mine = List.map (fun _ -> fresh st loc) params in
      if Check_unify.unify (T.Tuple (List.map snd ps)) (T.Tuple mine) then
        T.resolve (T.Fn (ps, ret, row))
      else expected
  | _ -> expected

let closure ctx expected loc (params : Hir.closure_param list) (body : Hir.expr)
    =
  let st = ctx.st in
  (* A closure expected to have the error type, or the wrong number of
     parameters, has the error type, and so do its parameters. *)
  let unknown =
    (List.map (fun _ -> (by_value, T.Error)) params, T.Error, T.fresh_row ())
  in
  let expected = Option.map (fit_arity st loc params) expected in
  let arity_ok, expected_fn =
    match Option.map T.resolve expected with
    | Some (Fn (ps, ret, row)) when List.length ps = List.length params ->
        (true, Some (ps, ret, row))
    | Some (Fn (ps, _, _)) ->
        error st Code.e0315 loc
          "this closure takes %d parameter%s, but %d %s expected"
          (List.length params)
          (if List.length params = 1 then "" else "s")
          (List.length ps)
          (if List.length ps = 1 then "is" else "are");
        (false, Some unknown)
    | Some Error -> (true, Some unknown)
    | _ -> (true, None)
  in
  let param_tys =
    match expected_fn with
    | Some (ps, _, _) -> List.map (fun (_, t) -> Some t) ps
    | None -> List.map (fun _ -> None) params
  in
  let patterns = List.map2 (closure_param ctx) params param_tys in
  (* An [inout] parameter makes an [inout] parameter of the closure's type
     (expressions.inout-closure-parameters). *)
  let modes = List.map (fun (p : Hir.closure_param) -> p.mode) params in
  let ret, row =
    match expected_fn with
    | Some (_, ret, row) -> (ret, row)
    | None -> (fresh st body.loc, T.fresh_row ~least:true ())
  in
  let known = (T.row_contents row).effects in
  let inner = { ctx with ret; yields = None; effects = ref []; known } in
  let b = Check_spreads.in_closure st (fun () -> check inner ret body) in
  settle st !(inner.effects) row;
  let ty =
    if arity_ok then
      T.Fn
        ( List.map2 (fun mode (p : A.pattern) -> (mode, p.pty)) modes patterns,
          ret,
          row )
    else T.Error
  in
  let written =
    List.filter_map (fun (p : Hir.closure_param) -> p.annotation) params
  in
  node (Closure (patterns, written, b)) ty loc
