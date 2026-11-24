(* The walk of a body's statements and expressions in source order, each with
   where its value goes. *)

open Tast
open Modes_flow

let is_param st (v : Hir.var) =
  match own st v with Some { kind = Param _; _ } -> true | _ -> false

(* Where a binding of this frame leaves the function (modes.escaping). A parameter
   that leaves is one its function consumes (values.consumed-parameters). *)
let leave st (v : Hir.var) =
  if is_param st v then st.flow.kept <- v.id :: st.flow.kept
  else st.flow.escapes <- v.id :: st.flow.escapes

(* The fields of a record literal, each at its place. *)
let fields_at fields =
  List.map (fun (n, x) -> (Some [ Modes_places.Field n ], x)) fields

(* Whether a callee is [std.sync]'s [Shared.new]. *)
let is_shared_new (c : callee) =
  match c with
  | Member ({ home = "std.sync"; name = "Shared" }, "new") -> true
  | _ -> false

let rec block ?id st (b : block) into =
  let id = match id with Some id -> id | None -> fresh_block st in
  let outer = st.blocks in
  st.blocks <- id :: outer;
  let n = List.length b in
  spanning st id (fun () ->
      List.iteri
        (fun i (s : stmt) ->
          match s.stmt with
          | Expr x when i + 1 = n -> expr st x into
          | Expr x | Assert x -> expr st x (read Here)
          | Let b -> binding st b Let id
          | Var b -> binding st b Var id
          | Assign (op, place, value) -> assign st (op <> None) place value
          | Yield place -> yield st place)
        b);
  st.blocks <- outer

(* A [yield] hands its place to the caller, who may modify it (projections.yield; projections.nested). *)
and yield st place =
  List.iter (fun x -> expr st x (read Here)) (Modes_places.place_parts place);
  expr st place (leaving Out);
  write st place

(* A [let] or [var] statement: its value is bound by its pattern, whose
   bindings last until their block ends, and start anew where the statement
   runs again (modes.shared-writes). Rebinding a parameter with [var]
   consumes it (values.consumed-parameters). *)
and binding st (b : Tast.binding) kind scope =
  let bound = binders b.pattern in
  bind_at st bound;
  let into =
    {
      (read Here) with
      held_by = Some (Bound (bound, Scope scope));
      pattern = Some b.pattern;
    }
  in
  expr st b.value into;
  (match (kind, b.value.desc) with
  | Var, Local v when is_param st v -> st.flow.kept <- v.id :: st.flow.kept
  | _ -> ());
  Option.iter (fun x -> expr st x (read Here)) b.otherwise;
  List.iter (fun v -> declare st v kind (Scope scope)) bound

(* An assignment to the whole of a local copies its value, held by the local
   until its scope ends (modes.copies); one to an [inout] parameter, to a part of a
   binding or through an index stores it in that binding (modes.escaping). Assigning
   a whole binding replaces its value, and every other assignment modifies it
   (modes.shared-writes). *)
and assign st compound place value =
  List.iter (fun x -> expr st x (read Here)) (Modes_places.place_parts place);
  let target = Modes_places.place place in
  let into =
    match target with
    | Some { root; path } when not compound -> (
        match Hashtbl.find_opt st.flow.decls root.id with
        | Some d when path = [] && not (is_param st root) ->
            { (read Here) with held_by = Some (Bound ([ root ], d.scope)) }
        | _ ->
            {
              (read Here) with
              leaves = Some Kept;
              held_by = Some (Place root);
              at = Some path;
            })
    | _ -> read Here
  in
  let start = (point st).tick in
  expr st value into;
  match target with
  | Some { root; path } when not compound -> (
      st.flow.assigned <-
        (root.id, path, start, (point st).tick) :: st.flow.assigned;
      match path with [] -> () | _ -> write ~replaces:true st place)
  | _ -> write st place

and expr st (e : expr) into =
  match Modes_places.place e with
  | Some { root; path } -> place st e root path into
  | None -> (
      match e.desc with
      | Record (_, _, fields) -> literal st (fields_at fields) into
      (* records.update: the base's fields go into the update, as a
         literal's do. *)
      | Update (base, fields) ->
          literal st ((Some [], base) :: fields_at fields) into
      | Construct (_, _, xs) ->
          literal st (List.map (fun x -> (None, x)) xs) into
      | Tuple xs ->
          literal st
            (List.mapi
               (fun i x -> (Some [ Modes_places.Field (string_of_int i) ], x))
               xs)
            into
      | List xs ->
          literal st
            (List.map (fun x -> (Some [ Modes_places.Index ], x)) xs)
            into
      | Closure (ps, _, body) ->
          Modes_flow_calls.closure ~expr st e ps body into
      | Call (c, _, args, _) | Project (c, _, args, _) ->
          args_of st args (st.calls.consumed c) ~named:true ~ty:e.ty into;
          if is_shared_new c then handed st e args
      | Call_value (f, args) ->
          expr st f (read Here);
          args_of st args [] ~named:false ~ty:e.ty into
      | Return (Some v) | Raise v ->
          expr st v (leaving Out);
          ignore (jump st)
      | Return None -> ignore (jump st)
      | Break | Continue -> Modes_flow_calls.leave st e
      | Block b -> block st b into
      | If (c, b, alt) ->
          expr st c (read Here);
          Modes_flow_calls.either st
            (fun () -> block st b into)
            (fun () -> Option.iter (fun x -> expr st x into) alt)
      | Else (a, b) ->
          expr st a into;
          Modes_flow_calls.either st (fun () -> expr st b into) ignore
      | Binary ((And | Or), a, b) ->
          expr st a (read Here);
          Modes_flow_calls.either st (fun () -> expr st b (read Here)) ignore
      | Spread _ -> Modes_flow_calls.again st (fun () -> parts st e (read Here))
      | With _ -> Modes_flow_calls.handled st (fun () -> parts st e (read Here))
      | When (names, b) -> held st e names b into
      | If_let _ | Match _ | Try _ -> branches st e into
      | Loop _ | While _ | For _ -> looping st e
      (* meta.erasure: an annotated form's value goes where the form's
         does. *)
      | Comptime x -> expr st x into
      | _ -> parts st e (read Here))

and parts st e into =
  List.iter
    (function Walk.Expr x -> expr st x into | Block b -> block st b into)
    (Walk.parts e)

(* A place whose value goes where [into] says: a binding of this frame with a
   value of a copy-on-write type escapes, is copied, or is passed to a call
   that may lose its reuse. A part of a binding's own value that goes back into
   the binding, directly or through a call whose result it holds, is no copy,
   but the binding's copies made before carry over to it
   (modes.shared-self-parts). A captured binding of an enclosing frame is copied
   too, so that its copies count where it is read when the closure ends. *)
and place st e (root : Hir.var) path into =
  List.iter (fun x -> expr st x (read Here)) (Modes_places.place_parts e);
  st.flow.reads <- (root.id, point st) :: st.flow.reads;
  let into_itself =
    List.exists
      (fun h -> List.exists (fun (v : Hir.var) -> v.id = root.id) (holders h))
      (Option.to_list into.held_by @ Option.to_list into.result)
  in
  let cow = st.calls.cow e.ty in
  match own st root with
  | Some _ when cow && into_itself ->
      if into.held_by = None && into.leaves <> None then leave st root;
      st.flow.selves <-
        (root.id, path, into.at, (point st).tick) :: st.flow.selves
  | Some _ when cow ->
      let made = point st in
      if into.leaves <> None then leave st root;
      copies st root path made into;
      Option.iter
        (fun r -> st.passed <- (root, path, made, r, e) :: st.passed)
        into.result
  | None when cow && (not into_itself) && Hashtbl.mem st.flow.decls root.id ->
      copies st root path (point st) into
  | _ -> ()

(* The copies of a part of a binding that a value going where [into] says
   makes (modes.copies). *)
and copies st (root : Hir.var) path made into =
  match (into.held_by, into.pattern) with
  | Some (Bound (_, ext)), Some pattern ->
      List.iter
        (fun (part, v, ty) ->
          if st.calls.cow ty then
            copy ~at:(Some []) st root.id part made (Bound ([ v ], ext)) false)
        (pattern_parts pattern path)
  | Some holder, _ ->
      copy ~at:into.at st root.id path made holder (into.leaves <> None)
  | None, _ -> ()

(* A literal stores each of its elements in a value that what holds the
   literal holds, at the element's place inside it if it has one. *)
and literal st elements into =
  List.iter
    (fun (step, x) ->
      let at =
        match (into.at, step) with
        | Some at, Some step -> Some (at @ step)
        | _ -> None
      in
      expr st x
        {
          (read into.lasts) with
          leaves = Some Kept;
          held_by = Some (keeper into);
          at;
        })
    elements

(* The arguments of a call, from left to right. A binding passed to a
   consumed parameter escapes (modes.escaping), and the call copies it when it loses
   its reuse; when it doesn't, the binding passes on the copies it holds, as a
   copy of it would. An argument that the call may store is copied, without
   escaping (modes.call-stores). Each lasts as the call's result does, and as each binding
   that an [inout] argument is a part of, where the call may store it
   (modes.copies). An [inout] argument doesn't escape (modes.not-escaping): the
   call modifies it. *)
and args_of st args consumed ~named ~ty into =
  let outer = st.passed in
  st.passed <- [];
  let before = st.flow.copies in
  let result = keeper into in
  let targets =
    ty
    :: List.filter_map
         (fun (a : arg) -> if a.mode = Ast.Inout then Some a.value.ty else None)
         args
  in
  List.iteri
    (fun i (a : arg) ->
      if a.mode = Ast.Inout then
        List.iter
          (fun x -> expr st x (read Here))
          (Modes_places.place_parts a.value)
      else if named && List.mem i consumed then
        expr st a.value
          {
            (read Here) with
            leaves = Some Kept;
            result = Some result;
            at = None;
          }
      else if st.calls.may_store a.value.ty targets then
        expr st a.value { (read Here) with result = Some result; at = None }
      else expr st a.value (read Here))
    args;
  List.iter
    (fun ((root : Hir.var), path, made, holder, (_ : expr)) ->
      copy st root.id path made holder true)
    st.passed;
  st.passed <- outer;
  stored_in_inouts st args ~before result;
  List.iter (fun (a : arg) -> if a.mode = Ast.Inout then write st a.value) args

(* The copies that the arguments passed to consumed parameters made, held by
   the call's result, held as well by each binding that an [inout] argument is
   a part of, at no known place in it (modes.copies). *)
and stored_in_inouts st args ~before result =
  let rec made_since = function
    | l when l == before -> []
    | c :: rest -> c :: made_since rest
    | [] -> []
  in
  let roots =
    List.filter_map
      (fun (a : arg) ->
        if a.mode = Ast.Inout then
          Option.map
            (fun (p : Modes_places.place) -> p.root)
            (Modes_places.place a.value)
        else None)
      args
  in
  let made =
    List.filter (fun c -> c.holder == result) (made_since st.flow.copies)
  in
  List.iter
    (fun c ->
      List.iter
        (fun r ->
          st.flow.copies <-
            { c with holder = Place r; stored = true; at = None }
            :: st.flow.copies)
        roots)
    made

(* A [when]'s names stand for the places of the shared values, which its
   block may modify as a [var] (shared.when): each is bound where the block
   starts. Its value goes back to the handle when the block ends, where later
   [when]s may write it, so what it holds lasts on, and the end of the block
   modifies each name (modes.handles). The block's value is the [when]'s, held
   by what holds it, so that a copy of a name the block gives lasts there. *)
and held st (e : expr) names b into =
  List.iter (fun (x, _) -> expr st x (read Here)) names;
  join_names st names;
  let id = fresh_block st in
  let vars = List.map snd names in
  bind_at st vars;
  List.iter (fun v -> declare st v Var Rest) vars;
  block ~id st b { into with held_by = Some (keeper into) };
  let at = point st in
  List.iter
    (fun (v : Hir.var) ->
      st.flow.writes <-
        { target = v.id; wpath = []; at; place = e; replaces = false }
        :: st.flow.writes)
    vars

(* modes.handles: a call of [Shared.new] shares the value it is given with the
   handle, where later [when]s may write it: a write of the binding whose value
   it is, if the argument names one. *)
and handed st (e : expr) args =
  match args with
  | [ (a : arg) ] -> (
      match Modes_places.place a.value with
      | Some { root; path } ->
          st.flow.handed <-
            {
              target = root.id;
              wpath = path;
              at = point st;
              place = e;
              replaces = false;
            }
            :: st.flow.handed
      | None -> ())
  | _ -> ()

and branches st e into = Modes_flow_calls.branches ~block ~expr st e into
and looping st e = Modes_flow_calls.looping ~block ~expr st e

(* modes.shared-when-names: a modification and a read of one name of a [when]
   are one of each name whose value has the same type, which may be its place;
   an assignment of one replaces nothing of the others. *)
let join flow =
  let other v (a, b) =
    if v = a then Some b else if v = b then Some a else None
  in
  let writes =
    List.concat_map
      (fun pair ->
        List.filter_map
          (fun w ->
            Option.map (fun u -> { w with target = u }) (other w.target pair))
          flow.writes)
      flow.joined
  in
  let reads =
    List.concat_map
      (fun pair ->
        List.filter_map
          (fun (v, at) -> Option.map (fun u -> (u, at)) (other v pair))
          flow.reads)
      flow.joined
  in
  flow.writes <- flow.writes @ writes;
  flow.reads <- flow.reads @ reads

let walk calls ~params b =
  let st = create calls in
  List.iter (fun (mode, v) -> declare st v (Param mode) Rest) params;
  block st b (leaving Out);
  st.flow.ticks <- st.tick;
  join st.flow;
  st.flow
