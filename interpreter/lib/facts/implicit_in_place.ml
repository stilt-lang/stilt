(* Updates in place (facts.own-storage, facts.writes-in-place and facts.copy-at-call): which bindings hold their own
   storage, which writes through an index are in place, and which arguments a
   call copies for a callee that updates them in place. *)

open Tast
module N = Implicit_names

type context = {
  env : Env.t;
  params : (Ast.mode * Hir.var) list;
  limited : bool;
  last : Modes_last.t;
  shared : Modes_shared.shared list;
  in_place : N.key -> (int * Ast.mode) list;
}

type result = {
  writes : expr list;
  copies : (expr * string) list;
  reasons : (expr * string) list;
  reached : int list;
}

(* facts.own-storage: what an assignment of a whole binding gives it, its
   declaration among them: a parameter's storage, a value, or parts of a value
   that a pattern takes apart. *)
type given = Param of Hir.var | Value of Hir.var * expr | Apart of Hir.var

(* A point of the body: its tick, in the order the walk meets expressions, which
   is source order, and the loops it is inside. *)
type point = { tick : int; loops : int list }

type assignment = {
  took : int;  (** Where it takes effect. *)
  mutable holds : int;
      (** The last tick of the block it is a statement of, which holds every
          point from [took] to there. *)
  inside : int list;  (** The loops it is inside. *)
  given : given;
}

type event =
  | Write of expr * expr * point  (** A binding [b] and the place written. *)
  | Window of expr * expr  (** A call of [view.into] or [view.split]. *)
  | Pass of callee * arg * Ast.mode
      (** An argument to an in-place parameter. *)

type state = {
  cx : context;
  assigned : (int, assignment list) Hashtbl.t;
  points : (Ast.loc, point) Hashtbl.t;
      (* The first point at each position: that of the outermost expression
         written there. *)
  mutable tick : int;
  mutable loops : int list;
  mutable loop_count : int;
  mutable block_assigned : assignment list;
  mutable events : event list;
  mutable writes : expr list;
  mutable copies : (expr * string) list;
  mutable reasons : (expr * string) list;
  mutable reached : int list;
}

let is_list ty =
  match Types.resolve ty with
  | Con (item, _) -> item = Types.prelude_item "List"
  | _ -> false

let here (st : state) : point = { tick = st.tick; loops = st.loops }
let point_of st (e : expr) = Hashtbl.find_opt st.points e.loc

(* facts.own-storage: the assignments of [v] before [at]: the last one before it
   that is a statement of a block holding it, each one after that and before
   [at], and when [at] is inside a loop that the last one is outside of, each
   one inside the loop. *)
let before st (v : Hir.var) (at : point) =
  let all = Option.value (Hashtbl.find_opt st.assigned v.id) ~default:[] in
  let holding =
    List.filter (fun a -> a.took <= at.tick && at.tick <= a.holds) all
  in
  match List.sort (fun a b -> compare b.took a.took) holding with
  | [] -> None
  | last :: _ ->
      let looped =
        List.filter (fun l -> not (List.mem l last.inside)) at.loops
      in
      Some
        (List.filter
           (fun a ->
             (last.took <= a.took && a.took <= at.tick)
             || List.exists (fun l -> List.mem l a.inside) looped)
           all)

(* facts.own-storage: whether [v] holds its own storage at [at], with the
   parameters whose storage it may hold, or why it doesn't. *)
let rec holds st (v : Hir.var) (at : point) :
    (Hir.var list, string) Stdlib.result =
  match before st v at with
  | None -> Error (Printf.sprintf "`%s` is bound by a pattern" v.name)
  | Some assignments ->
      List.fold_left
        (fun acc a ->
          match (acc, judge st a.given) with
          | Ok xs, Ok ys -> Ok (xs @ ys)
          | (Error _ as e), _ | _, (Error _ as e) -> e)
        (Ok []) assignments

(* facts.own-storage: whether an assignment gives its binding storage of its
   own. *)
and judge st given : (Hir.var list, string) Stdlib.result =
  match given with
  | Param v when st.cx.limited -> Ok [ v ]
  | Param v ->
      Error
        (Printf.sprintf
           "`%s` is a parameter of a function not limited by `without alloc`, \
            whose callers may share it"
           v.name)
  | Apart v -> Error (Printf.sprintf "`%s` is bound by a pattern" v.name)
  | Value (_, { desc = List _; _ }) -> Ok []
  | Value (v, ({ desc = Local u; _ } as value))
    when not (Modes_last.is_last st.cx.last value) ->
      Error
        (Printf.sprintf "`%s` takes `%s`, which is used again" v.name u.name)
  | Value (v, ({ desc = Local u; _ } as value)) -> (
      match point_of st value with
      | None -> Error (Printf.sprintf "`%s` takes `%s`" v.name u.name)
      | Some at ->
          Result.map_error
            (fun why ->
              Printf.sprintf "`%s` takes `%s`, and %s" v.name u.name why)
            (holds st u at))
  | Value (v, _) ->
      Error
        (Printf.sprintf
           "`%s` holds a value that isn't a list literal or a binding at its \
            last use"
           v.name)

let shared st (place : expr) =
  List.find_opt (fun (s : Modes_shared.shared) -> s.place == place) st.cx.shared
  |> Option.map (fun (s : Modes_shared.shared) ->
      match (s.holder, Modes_places.place place) with
      | Some h, Some p ->
          Printf.sprintf "a copy of `%s` that `%s` holds lasts here" p.root.name
            h.name
      | _, Some p ->
          Printf.sprintf "a copy of `%s` made in this loop lasts here"
            p.root.name
      | _ -> "a copy of it lasts here")

let reach st = List.iter (fun (p : Hir.var) -> st.reached <- p.id :: st.reached)

(* facts.writes-in-place: whether a write to the binding [e] names, modifying [place], is in
   place: the binding holds its own storage at [at], and modes.shared-writes doesn't
   make the modification shared. *)
let in_place st (e : expr) place at : (unit, string) Stdlib.result =
  match (e.desc, at) with
  | Local v, Some at -> (
      match (holds st v at, shared st place) with
      | Ok origins, None ->
          reach st origins;
          Ok ()
      | Error why, _ | Ok _, Some why -> Error why)
  | _ -> Error "it isn't a binding named whole"

let callee_name env c =
  Option.fold ~none:"it" ~some:N.show_key (N.callee_key env c)

(* facts.copy-at-call: the copy at a call of an argument to an in-place parameter. *)
let argument st c (a : arg) mode =
  let through = function
    | Some (p : Modes_places.place) -> List.mem Modes_places.Index p.path
    | None -> false
  in
  let outcome =
    match ((mode : Ast.mode), a.value.desc) with
    | Inout, _ when through (Modes_places.place a.value) -> Ok ()
    (* facts.copy-at-call: a list literal is a value that nothing else holds. *)
    | Let, List _ -> Ok ()
    | Inout, _ -> in_place st a.value a.value (point_of st a.value)
    | Let, Local v when not (Modes_last.is_last st.cx.last a.value) ->
        Error (Printf.sprintf "`%s` is used again after the call" v.name)
    | Let, Local v -> (
        match point_of st a.value with
        | Some at -> Result.map (reach st) (holds st v at)
        | None -> Error "the argument isn't a binding named whole")
    | Let, _ -> Error "the argument isn't a binding named whole"
  in
  match outcome with
  | Ok () -> ()
  | Error why ->
      st.copies <-
        ( a.value,
          Printf.sprintf
            "this argument is copied for `%s`, which updates it in place: %s"
            (callee_name st.cx.env c) why )
        :: st.copies

let view_write = function
  | Function { home = "std.view"; name = "into" | "split" } -> true
  | _ -> false

let call st (e : expr) c args =
  match (view_write c, args) with
  | true, (a : arg) :: _ when a.mode = Inout ->
      (* projections.writable-views, and projections.yield *)
      st.events <- Window (e, a.value) :: st.events
  | _ -> (
      match N.callee_key st.cx.env c with
      | None -> ()
      | Some key ->
          List.iter
            (fun (i, mode) ->
              Option.iter
                (fun a -> st.events <- Pass (c, a, mode) :: st.events)
                (List.nth_opt args i))
            (st.cx.in_place key))

(* Whether a list's elements are of a type that isn't copy-on-write (modes.copy-on-write-types), so that nothing an element holds is shared with another. *)
let plain_elements env ty =
  match Types.resolve ty with
  | Con (_, [ elem ]) -> not (Modes_cow.is_cow env elem)
  | _ -> false

(* facts.writes-in-place: the list [b] that a write's place [b[i]] names, or one whose place
   goes on from [b[i]] through fields, tuple elements and elements of arrays,
   when the list's elements aren't of a copy-on-write type. *)
let rec written_list env ~inside (place : expr) =
  match place.desc with
  | Index (({ desc = Local _; _ } as b), _)
    when is_list b.ty && ((not inside) || plain_elements env b.ty) ->
      Some b
  | Index (base, _) when Option.is_some (Check_arrays.parts base.ty) ->
      written_list env ~inside:true base
  | Field (base, _) | Tuple_field (base, _) ->
      written_list env ~inside:true base
  | _ -> None

(* Records the assignment of a whole binding that a statement makes, which
   holds the points of its block after it. *)
let assigned st (v : Hir.var) given =
  let a = { took = st.tick; holds = max_int; inside = st.loops; given } in
  st.block_assigned <- a :: st.block_assigned;
  Hashtbl.replace st.assigned v.id
    (a :: Option.value (Hashtbl.find_opt st.assigned v.id) ~default:[])

let in_loop st f =
  let outer = st.loops in
  st.loop_count <- st.loop_count + 1;
  st.loops <- st.loop_count :: outer;
  f ();
  st.loops <- outer

let rec expr st (e : expr) =
  st.tick <- st.tick + 1;
  if not (Hashtbl.mem st.points e.loc) then
    Hashtbl.replace st.points e.loc (here st);
  (match e.desc with Call (c, _, args, _) -> call st e c args | _ -> ());
  match e.desc with
  | While (c, b) ->
      in_loop st (fun () ->
          expr st c;
          block st b)
  | Loop b -> in_loop st (fun () -> block st b)
  | For (_, Iter source, b) ->
      expr st source;
      in_loop st (fun () -> block st b)
  | For (_, Range (a, z, _), b) ->
      expr st a;
      expr st z;
      in_loop st (fun () -> block st b)
  | _ ->
      List.iter
        (function Walk.Expr x -> expr st x | Block b -> block st b)
        (Walk.parts e)

and block st b =
  let outer = st.block_assigned in
  st.block_assigned <- [];
  List.iter (stmt st) b;
  List.iter (fun a -> a.holds <- st.tick) st.block_assigned;
  (* The block's end is a tick of its own, which no point after it holds. *)
  st.tick <- st.tick + 1;
  st.block_assigned <- outer

and stmt st (s : stmt) =
  let at = here st in
  List.iter (expr st) (Walk.stmt_exprs s);
  match s.stmt with
  | Let { pattern = { pat = P_bind v; _ }; value; _ }
  | Var { pattern = { pat = P_bind v; _ }; value; _ } ->
      assigned st v (Value (v, value))
  | Let { pattern; _ } | Var { pattern; _ } ->
      List.iter
        (fun (v : Hir.var) -> assigned st v (Apart v))
        (Modes_flow.binders pattern)
  | Assign (None, { desc = Local v; _ }, value) ->
      assigned st v (Value (v, value))
  | Assign (_, place, _) -> (
      match written_list st.cx.env ~inside:false place with
      | Some b -> st.events <- Write (b, place, at) :: st.events
      | None -> ())
  | _ -> ()

(* facts.writes-in-place and facts.copy-at-call, decided once every assignment
   of the body is known. *)
let decide st = function
  | Write (b, place, at) -> (
      match in_place st b place (Some at) with
      | Ok () -> st.writes <- place :: st.writes
      | Error why -> st.reasons <- (place, why) :: st.reasons)
  | Window (e, a) -> (
      match in_place st a a (point_of st a) with
      | Ok () -> st.writes <- e :: st.writes
      | Error why -> st.reasons <- (e, why) :: st.reasons)
  | Pass (c, a, mode) -> argument st c a mode

let param st (_, (v : Hir.var)) =
  Hashtbl.replace st.assigned v.id
    (* facts.own-storage: a parameter's declaration, where the body starts. *)
    [ { took = 0; holds = max_int; inside = []; given = Param v } ]

let run cx b =
  let st =
    {
      cx;
      assigned = Hashtbl.create 16;
      points = Hashtbl.create 64;
      tick = 0;
      loops = [];
      loop_count = 0;
      block_assigned = [];
      events = [];
      writes = [];
      copies = [];
      reasons = [];
      reached = [];
    }
  in
  List.iter (param st) cx.params;
  block st b;
  List.iter (decide st) (List.rev st.events);
  {
    writes = st.writes;
    copies = List.rev st.copies;
    reasons = st.reasons;
    reached =
      List.concat
        (List.mapi
           (fun i (_, (v : Hir.var)) ->
             if List.mem v.id st.reached then [ i ] else [])
           cx.params);
  }
