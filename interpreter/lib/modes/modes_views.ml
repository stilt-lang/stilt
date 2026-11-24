(* The reads that views make (views.reads-that-last, views.change-while-viewed and views.for-over-view), and the writes of
   writable bindings (projections.what-view-writes), which the law of exclusivity weighs
   with the other accesses of a body (modes.law). *)

open Tast
module S = Views_sources

type read = {
  place : Modes_places.place;
  view : string;
  until : int Lazy.t;
  scope : int;
  writes : bool;
}

type t = {
  sources : S.t;
  mutable live : read list;
  mutable next : int;
  bindings : (int, int * int Lazy.t) Hashtbl.t;
}

let create block =
  {
    sources = S.collect block;
    live = [];
    next = 0;
    bindings = Hashtbl.create 8;
  }

let scope t =
  t.next <- t.next + 1;
  t.next

let close t scope = t.live <- List.filter (fun r -> r.scope <> scope) t.live

(* The last line that holds code of the expressions, which only a message
   needs. *)
let lines es =
  let last = ref 0 in
  List.iter (Walk.iter (fun (e : expr) -> last := max !last e.loc.line)) es;
  !last

let last_line es = lazy (lines es)
let stmt_line (s : stmt) = max s.at.line (lines (Walk.stmt_exprs s))
let stmt_last s = lazy (stmt_line s)
let block_last b = lazy (List.fold_left (fun m s -> max m (stmt_line s)) 0 b)

(* A read of each place among the sources of [value], until the line [until]
   and the end of [scope]; for a writable binding, a write of each place its
   view writes (projections.what-view-writes). A temporary can't change. *)
let read ?(writes = false) t ~view ~until ~scope value =
  List.iter
    (function
      | S.Place place ->
          t.live <- { place; view; until; scope; writes = false } :: t.live
      | S.Written place ->
          t.live <- { place; view; until; scope; writes } :: t.live
      | Temporary _ -> ())
    (S.sources t.sources value)

(* views.reads-that-last: a view that no binding holds reads its sources from where the
   call that makes it returns until the end of the statement that holds it,
   which is [stmt]. *)
let made t (scope, until) (e : expr) =
  if Views_types.is_view e.ty then
    read t
      ~view:(Printf.sprintf "the view made on line %d" e.loc.line)
      ~until ~scope e

(* views.reads-that-last: the read of a source that a [let] argument [a] gives
   the view that the call [e] returns begins once [a] is evaluated, before the
   arguments after it, and lasts at least until the end of the statement, as
   [made]'s does. It comes after the reads in progress, so a change that one of
   them meets names that one. *)
let operand t (scope, until) (e : expr) (a : arg) =
  if Views_types.is_view e.ty && a.mode = Let then
    let view = Printf.sprintf "the view made on line %d" e.loc.line in
    t.live <-
      t.live
      @ List.filter_map
          (function
            | S.Place place ->
                Some { place; view; until; scope; writes = false }
            | Written _ | Temporary _ -> None)
          (S.argument t.sources a)

(* views.reads-that-last: a binding of a view type, or of a closure that captures one (views.fixed), reads its sources for its scope, which is [scope] until the line
   [until]; a view assigned to it later reads its own from there on. *)
let bound t ~scope ~until (s : stmt) =
  let writable v =
    match Hashtbl.find_opt t.sources v with
    | Some b -> b.writable
    | None -> false
  in
  match s.stmt with
  | Let b | Var b -> (
      match
        List.filter (Hashtbl.mem t.sources)
          (Modes_places.pattern_vars b.pattern)
      with
      | [] -> ()
      | vars ->
          List.iter (fun v -> Hashtbl.replace t.bindings v (scope, until)) vars;
          let view =
            match b.pattern.pat with
            | P_bind v -> Printf.sprintf "`%s`" v.name
            | _ -> Printf.sprintf "the views bound on line %d" s.at.line
          in
          let writes = List.exists writable vars in
          read ~writes t ~view ~until ~scope b.value)
  | Assign (None, { desc = Local v; _ }, value) -> (
      match Hashtbl.find_opt t.bindings v.id with
      | Some (scope, until) ->
          read ~writes:(writable v.id) t
            ~view:(Printf.sprintf "`%s`" v.name)
            ~until ~scope value
      | None -> ())
  | Assign _ | Assert _ | Yield _ | Expr _ -> ()

(* views.change-while-viewed: the read of a view that a modification of [p] meets, or the write
   that any access meets (projections.what-view-writes); a write first, since a writable
   binding's own views read it. *)
let conflict ?(writing = true) t p =
  let hits r = Modes_places.overlap p r.place in
  match List.find_opt (fun r -> r.writes && hits r) t.live with
  | Some w -> Some w
  | None -> if writing then List.find_opt hits t.live else None
