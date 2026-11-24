(* Bodies of functions, tests and doc examples, each checked on its own. *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_effects
open Check_types
open Check_blocks
open Check_finish
open Check_zonk

(* errors.unknown-names: the body known by [at] keeps one E0211 for each name that
   doesn't resolve in it, where that name starts first, among those of the
   names that its patterns write without a module and those that resolution
   held back for the same names. *)
let settle_unknown_names st ~at =
  let held =
    List.filter_map
      (fun (body, name, d) -> if body = at then Some (name, d) else None)
      st.module_.held
  in
  let found = st.unknown_names @ held in
  let earliest name =
    List.fold_left
      (fun best (n, (d : Diagnostic.t)) ->
        match best with
        | _ when n <> name -> best
        | Some (b : Diagnostic.t)
          when compare (b.line, b.col) (d.line, d.col) <= 0 ->
            best
        | _ -> Some d)
      None found
  in
  let kept (name, d) = earliest name = Some d in
  let dropped = List.filter (fun u -> not (kept u)) st.unknown_names in
  st.errors <-
    List.filter
      (fun e -> not (List.exists (fun (_, d) -> d == e) dropped))
      st.errors;
  List.iter
    (fun ((_, d) as u) -> if kept u then st.errors <- d :: st.errors)
    held;
  st.unknown_names <- []

(* The elaboration of the body known by [at], or [Broken] if resolving or
   checking it found an error, so that the later phases skip it (errors.broken-parts). *)
let outcome st ~at elaborate : _ A.definition =
  settle_unknown_names st ~at;
  if
    st.errors = [] && (not st.broken) && not (List.mem at st.module_.unresolved)
  then Code (elaborate ())
  else Broken

let visible_traits env (m : Hir.module_) =
  Env.traits_of env "std.prelude"
  @ (if m.name = "std.prelude" then [] else Env.traits_of env m.name)
  @ List.concat_map (Env.traits_of env) m.imports

let new_state env (m : Hir.module_) ~bounds ~self =
  {
    env;
    module_ = m;
    traits = visible_traits env m;
    bounds;
    self;
    locals = Hashtbl.create 16;
    errors = [];
    broken = false;
    vars = [];
    unknown = [];
    obligations = [];
    fixes = [];
    operators = [];
    amounts = [];
    int_patterns = [];
    literals = [];
    units = [];
    specs = [];
    constants = [];
    catch_errors = [];
    passed = [];
    bare = Hashtbl.create 8;
    arrays = Hashtbl.create 8;
    unknown_names = [];
    needs = [];
    spreading = None;
    splices = [];
    unsafe_depth = 0;
    unsafe_blocks = [];
    c_elements = [];
  }

(* tasks.sequential-run: [main] and tests run under [task.sequential()] when no
   [with] installs another handler, which handles their [async]. *)
let sequential = T.Effect_of (T.async_effect, [])

(* A function's written body, checked against its signature. *)
let fn_body st (m : Hir.module_) (s : Env.fn_sig) (f : Hir.fn_decl) block =
  (* A projection's body has type [()], and yields its result type (projections.yield). *)
  let ret, yields =
    if s.projection then (T.unit, Some s.ret) else (s.ret, None)
  in
  let known = (T.row_contents s.row).effects in
  let ctx =
    {
      st;
      ret;
      yields;
      effects = ref [];
      infer = Check_exprs.infer;
      known;
      resume = None;
    }
  in
  let b, _ = block_expr ctx ~at:f.name.loc (Some ret) block in
  (* handlers.no-effect-reaches-main, and tasks.sequential-run: no user-defined effect reaches
     [main], which runs under [task.sequential()]. *)
  let main = m.name = "main" && (not m.std) && f.name.desc = "main" in
  if main then
    settle ~unhandled:true ~handled:sequential st !(ctx.effects) s.row
  else settle st !(ctx.effects) s.row;
  finish st;
  outcome st ~at:f.name.loc (fun () -> zonk_block b)

(* A function's body, checked against its signature. In the standard
   library, a hole body marks a native function (declarations.native-items); anywhere else it is
   a hole of the function's return type (declarations.typed-holes). *)
let check_fn env m ~bounds ~self (s : Env.fn_sig) (f : Hir.fn_decl) body =
  (* traits.where: the body assumes its [where] clause's bounds on its
     impl block's member types. *)
  let assumed =
    List.filter_map
      (fun (t, b) ->
        match t with Types.Param v -> Some (v, [ b ]) | _ -> None)
      s.assumed
  in
  let st = new_state env m ~bounds:(bounds @ s.type_params @ assumed) ~self in
  let params =
    List.map2
      (fun (p : Hir.param) (mode, ty) ->
        let v = match p with Self_param (_, v, _) | Param (_, v, _, _) -> v in
        Hashtbl.replace st.locals v.id ty;
        (mode, v))
      f.params s.params
  in
  let close =
    match body with Hir.Body (_, close) -> Some close | Body_hole _ -> None
  in
  let body : A.block A.definition =
    match body with
    | Hir.Body_hole _ when m.std -> Native
    | Body_hole loc -> Code [ { stmt = Expr (node Hole s.ret loc); at = loc } ]
    | Body (block, _) -> fn_body st m s f block
  in
  let limits = List.map (fun (l : Hir.limit Hir.node) -> l.desc) f.limits in
  let through =
    List.concat
      (List.map2
         (fun (_, v) passes -> if passes then [ v ] else [])
         params (Env.passing s))
  in
  ( {
      A.home = m.name;
      at = f.name.loc;
      params;
      type_params = List.map fst s.type_params;
      through;
      pairs = pairs s;
      passed = st.passed;
      limits;
      yields = (if s.projection then close else None);
      unsafe_blocks = List.rev st.unsafe_blocks;
      body;
    },
    st.errors )

(* c.foreign-functions: a foreign function, which C gives, and which has no body
   to check. Its limits are what its declaration's [without] clause says its C
   code doesn't do (c.effects). *)
let foreign_fn (m : Hir.module_) (s : Env.fn_sig) (f : Hir.fn_decl) =
  let var : Hir.param -> Hir.var = function
    | Self_param (_, v, _) | Param (_, v, _, _) -> v
  in
  {
    A.home = m.name;
    at = f.name.loc;
    params = List.map2 (fun p (mode, _) -> (mode, var p)) f.params s.params;
    type_params = List.map fst s.type_params;
    through = [];
    pairs = [];
    passed = [];
    limits = List.map (fun (l : Hir.limit Hir.node) -> l.desc) f.limits;
    yields = None;
    unsafe_blocks = [];
    body = Native;
  }

(* Checks a test's body or a doc example, which may perform [io] and raise
   any error that can be shown (program.test-declarations and program.doc-examples). What [check_body]
   returns is checked with the context it is given. *)
let check_test_body ?handled env m loc ~ret check_body =
  let st = new_state env m ~bounds:[] ~self:None in
  let error_ty = T.fresh loc in
  obligation st error_ty (prelude_trait "Show") loc;
  let ctx =
    {
      st;
      ret;
      yields = None;
      effects = ref [];
      infer = Check_exprs.infer;
      known = [];
      resume = None;
    }
  in
  let result = check_body ctx in
  settle ~unhandled:true ?handled st !(ctx.effects)
    { io = true; raise = Some error_ty; effects = []; tail = Closed };
  (* A body that raises nothing raises [Never]. *)
  if Option.is_some (T.unsolved error_ty) then T.solve error_ty T.never;
  finish st;
  let result = outcome st ~at:loc result in
  (result, st.errors)

let check_test env m loc block =
  check_test_body ~handled:sequential env m loc ~ret:T.unit (fun ctx ->
      let b, _ = block_expr ctx ~at:loc (Some T.unit) block in
      fun () -> zonk_block b)

let check_example env m (e : Hir.expr) =
  check_test_body env m e.loc ~ret:T.bool (fun ctx ->
      let claim = check ctx T.bool e in
      fun () -> zonk_expr claim)
