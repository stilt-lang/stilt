(* Modes and exclusivity: the errors of a body. *)

open Tast
open Modes_places

type ctx = {
  modifiable : int list;  (** The variables the code may modify. *)
  iterating : place list;  (** The places the enclosing [for] loops read. *)
  views : Modes_views.t;  (** The reads of views (views.reads-that-last). *)
  stmt : int * int Lazy.t;
      (** The scope of the statement that holds the code, and its last line. *)
}

(* projections.what-view-writes: an access of [p] that meets the write of a writable
   binding is E0429, which is counted as E0404 is (modes.change-while-iterating). *)
let writing report (e : expr) p (r : Modes_views.read) =
  report Code.e0429 e.loc
    (Printf.sprintf
       "`%s` can't be reached while %s writes through it, until line %d; reach \
        it before the view, or end the view's scope first"
       p.root.name r.view (Lazy.force r.until))

(* The projection whose call a place is rooted in, with its arguments
   (projections.call-is-place). *)
let rec projection_root (e : expr) =
  match e.desc with
  | Project (_, _, args, _) -> Some args
  | Field (base, _) | Tuple_field (base, _) | Index (base, _) ->
      projection_root base
  | _ -> None

(* The [inout] parameters of a closure, which its type gives (expressions.inout-closure-parameters). *)
let closure_inouts (e : expr) params =
  match Types.resolve e.ty with
  | Fn (modes, _, _) when List.length modes = List.length params ->
      List.concat
        (List.map2
           (fun (mode, _) (p : pattern) ->
             match (mode, p.pat) with
             | Ast.Inout, P_bind v -> [ v.id ]
             | _ -> [])
           modes params)
  | _ -> []

(* A modification of [e], which is a place, if it is allowed at all, and the
   places it holds: the place itself, or for a projection's call, every
   place its [inout] arguments hold, for the whole access (projections.when-projection-runs).
   [report] reports an error. *)
let rec modify report ctx (e : expr) =
  let one p =
    if not (List.mem p.root.id ctx.modifiable) then (
      report Code.e0403 e.loc
        (Printf.sprintf
           "`%s` can't be modified here; only `var` bindings and `inout` \
            parameters of this body can"
           p.root.name);
      None)
    else (
      (* views.change-while-viewed: a change while a view reads the place is E0423,
         which is counted as E0404 is (modes.change-while-iterating). *)
      (if List.exists (overlap p) ctx.iterating then
         report Code.e0404 e.loc
           (Printf.sprintf
              "`%s` is being read by a `for` loop around this change"
              p.root.name)
       else
         match Modes_views.conflict ctx.views p with
         | Some r when r.writes -> writing report e p r
         | Some r ->
             report Code.e0423 e.loc
               (Printf.sprintf
                  "`%s` can't change while %s reads it, until line %d; make \
                   the change before the view, or end the view's scope first"
                  p.root.name r.view (Lazy.force r.until))
         | None -> ());
      Some p)
  in
  match projection_root e with
  | Some args -> call report ctx args
  | None -> Option.to_list (Option.bind (place e) one)

(* Arguments are evaluated first; the [inout] ones are modified from the
   start of the call, all together (modes.durations and modes.overlapping-inout). The places modified. *)
and call ?(operand = ignore) report ctx args =
  List.iter
    (fun (a : arg) ->
      if a.mode = Inout then List.iter (expr report ctx) (place_parts a.value)
      else expr report ctx a.value;
      operand a)
    args;
  let modified =
    List.concat_map
      (fun (a : arg) ->
        if a.mode = Inout then
          List.map (fun p -> (p, a.value.loc)) (modify report ctx a.value)
        else [])
      args
  in
  List.iteri
    (fun i (p, loc) ->
      if
        List.exists
          (fun (q, _) -> overlap p q)
          (List.filteri (fun j _ -> j < i) modified)
      then
        report Code.e0402 loc
          (Printf.sprintf "`%s` is already modified by this call" p.root.name))
    modified;
  List.map fst modified

(* A read of the place [e] (modes.kinds-of-access), which no write through a view
   may be in progress on (projections.what-view-writes). *)
and read report ctx (e : expr) =
  match place e with
  | Some p -> (
      match Modes_views.conflict ~writing:false ctx.views p with
      | Some r -> writing report e p r
      | None -> ())
  | None -> ()

(* views.reads-that-last: the view that a call returns reads each source from
   where the argument that gives it is evaluated, and the rest from where the
   call returns. *)
and expr report ctx (e : expr) =
  let operand = Modes_views.operand ctx.views ctx.stmt e in
  match e.desc with
  | Call (_, _, args, _) ->
      ignore (call ~operand report ctx args);
      Modes_views.made ctx.views ctx.stmt e
  | Project (_, _, args, _) ->
      (* A read of the call, whose place is held for the read (projections.when-projection-runs). *)
      ignore (call ~operand report ctx args);
      Modes_views.made ctx.views ctx.stmt e
  | Call_value (f, args) ->
      expr report ctx f;
      ignore (call ~operand report ctx args);
      Modes_views.made ctx.views ctx.stmt e
  | Closure (params, _, body) ->
      (* The views that the body makes are read where it runs. *)
      let modifiable = closure_inouts e params @ expr_var_bindings body in
      let scope = Modes_views.scope ctx.views in
      let until = Modes_views.last_line [ body ] in
      expr report { ctx with modifiable; stmt = (scope, until) } body;
      Modes_views.close ctx.views scope
  | When (held, b) ->
      List.iter (fun (h, _) -> expr report ctx h) held;
      let names = List.map (fun ((h : expr), v) -> (v, h.ty)) held in
      Modes_places.holding names (fun () -> block_ report ctx b)
  | For (_, Iter source, b) ->
      expr report ctx source;
      let iterating =
        match place source with
        | Some p -> p :: ctx.iterating
        | None -> ctx.iterating
      in
      block_ report { ctx with iterating } b
  | _ when place e <> None ->
      read report ctx e;
      List.iter (expr report ctx) (place_parts e)
  | _ ->
      List.iter
        (function
          | Walk.Expr e -> expr report ctx e | Block b -> block_ report ctx b)
        (Walk.parts e)

(* views.reads-that-last: a view that no binding holds is read until the end of
   its statement, and a binding's until the end of its scope. *)
and block_ report ctx b =
  let views = ctx.views in
  let scope = Modes_views.scope views in
  let until = Modes_views.block_last b in
  List.iter
    (fun (s : stmt) ->
      let ctx =
        { ctx with stmt = (Modes_views.scope views, Modes_views.stmt_last s) }
      in
      (match s.stmt with
      | Assign (_, p, v) ->
          List.iter (expr report ctx) (place_parts p);
          expr report ctx v;
          ignore (modify report ctx p)
      | Yield p when place p <> None || Check_fields.rooted_in_projection p ->
          (* The place is handed to the caller, who may modify it (projections.yield). *)
          List.iter (expr report ctx) (place_parts p);
          ignore (modify report ctx p)
      | Let _ | Var _ | Assert _ | Yield _ | Expr _ ->
          List.iter (expr report ctx) (Walk.stmt_exprs s));
      Modes_views.close views (fst ctx.stmt);
      Modes_views.bound views ~scope ~until s)
    b;
  Modes_views.close views scope

(* modes.law, modes.durations, modes.overlapping-inout, modes.closures and modes.what-can-be-modified, expressions.inout-closure-parameters and expressions.capture, and views.reads-that-last, views.change-while-viewed and views.for-over-view. A
   modification of what can't be modified is reported as that alone, and
   takes no part in modes.overlapping-inout. *)
let errors ~file ~params block =
  let found = ref [] in
  let report code loc message =
    found := Diagnostic.at ~file code loc message :: !found
  in
  let inout = List.map (fun (v : Hir.var) -> v.id) (inout_params params) in
  block_ report
    {
      modifiable = inout @ var_bindings block;
      iterating = [];
      views = Modes_views.create block;
      stmt = (0, lazy 0);
    }
    block;
  List.rev !found
