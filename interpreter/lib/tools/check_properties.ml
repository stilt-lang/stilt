(* tests.property-form, tests.property-checking and tests.generable-types. *)

module T = Types
module A = Tast
open Check_state
open Check_bodies

(* tests.property-form: the expression, or each parameter, that keeps a property from being
   a closure with typed parameters. A parameter marked [inout] is no pattern,
   so it is no parameter of a property either (expressions.closure-parameter-types and expressions.inout-closure-parameters). *)
let malformed (e : Hir.expr) =
  match e.desc with
  | Closure ((_ :: _ as params), _) ->
      List.filter_map
        (fun (p : Hir.closure_param) ->
          if p.annotation = None || p.mode = Inout then Some p.pattern.loc
          else None)
        params
  | _ -> [ e.loc ]

let reason = function
  | Prop_types.Function -> "it holds a function type"
  | No_values t -> Printf.sprintf "it holds `%s`, which has no values" (show t)
  | Key t ->
      Printf.sprintf
        "it holds a map keyed by `%s`, which doesn't implement both `Eq` and \
         `Hash`"
        (show t)
  | Infinite -> "it holds infinitely many types"

(* tests.generable-types: a parameter, whose type must be generable. *)
let param ctx (p : Hir.closure_param) =
  let st = ctx.st in
  let written = Option.get p.annotation in
  let ty = Check_types.of_hir st written in
  Option.iter
    (fun u ->
      error st Code.e0333 written.loc "values of `%s` can't be generated: %s"
        (show ty) (reason u))
    (Prop_types.unfit st.env ty);
  let checked = Check_patterns.pattern ctx p.pattern ty in
  Check_refutable.require_irrefutable st p.pattern;
  checked

(* tests.property-io: the body's effects fit a row of no [io] that raises [error], where
   the first call that performs [io] is E0510 rather than E0502. *)
let settle st effects error_ty =
  let row = { T.empty_row with raise = Some error_ty } in
  let report = Check_effects.reporter st in
  let io = ref false in
  List.iter
    (fun (r, loc) ->
      let problems = Check_unify.fit r row in
      let performs = function Check_unify.Missing_io -> true | _ -> false in
      if List.exists performs problems && not !io then (
        io := true;
        error st Code.e0510 loc "this performs `io`, which a property can't");
      report loc (List.filter (fun p -> not (performs p)) problems))
    (List.rev effects);
  row

let closure env m (e : Hir.expr) params body =
  let st = new_state env m ~bounds:[] ~self:None in
  let error_ty = T.fresh e.loc in
  obligation st error_ty (prelude_trait "Show") e.loc;
  let ctx =
    {
      st;
      ret = T.bool;
      yields = None;
      effects = ref [];
      infer = Check_exprs.infer;
      known = [];
      resume = None;
    }
  in
  let patterns = List.map (param ctx) params in
  let b = Check_expect.check ctx T.bool body in
  let row = settle st !(ctx.effects) error_ty in
  (* A body that raises nothing raises [Never]. *)
  if Option.is_some (T.unsolved error_ty) then T.solve error_ty T.never;
  Check_finish.finish st;
  let ty =
    T.Fn
      (List.map (fun (p : A.pattern) -> (by_value, p.pty)) patterns, T.bool, row)
  in
  let elaborated () =
    let written =
      List.filter_map (fun (p : Hir.closure_param) -> p.annotation) params
    in
    Check_zonk.zonk_expr (node (Closure (patterns, written, b)) ty e.loc)
  in
  let closure = outcome st ~at:e.loc elaborated in
  (closure, st.errors)

let check_property env (m : Hir.module_) (e : Hir.expr) =
  match (malformed e, e.desc) with
  | [], Closure (params, body) -> closure env m e params body
  | locs, _ ->
      let error loc =
        Diagnostic.at ~file:m.file Code.e0332 loc
          "a property is a closure with at least one parameter, each a pattern \
           with its type written"
      in
      (Broken, List.map error locs)
