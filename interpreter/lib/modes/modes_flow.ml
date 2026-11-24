(* The flow of values through a body, which locality and uniqueness read
   (modes.escaping, modes.not-escaping, modes.copies and modes.shared-writes). Positions are ticks, counted in the
   order the walk meets what it records, which is source order; a scope is
   the block that holds a binding, since a binding lasts until its block
   ends. *)

open Tast

type kind = Let | Var | Param of Ast.mode | Pattern
type extent = Here | Rest | Scope of int
type point = { tick : int; blocks : int list }
type decl = { var : Hir.var; kind : kind; frame : int; scope : extent }

type holder =
  | Bound of Hir.var list * extent
  | Place of Hir.var
  | Until of extent

type copy = {
  binding : int;
  path : Modes_places.step list;
  made : point;
  came : int;
  holder : holder;
  stored : bool;
  at : Modes_places.step list option;
  wide : bool;
}

type write = {
  target : int;
  wpath : Modes_places.step list;
  at : point;
  place : expr;
  replaces : bool;
}

type t = {
  decls : (int, decl) Hashtbl.t;
  mutable escapes : int list;
  mutable kept : int list;
  mutable held : (int list * int list) list;
  mutable copies : copy list;
  mutable writes : write list;
  mutable assigned : (int * Modes_places.step list * int * int) list;
  mutable reads : (int * point) list;
  mutable selves :
    (int * Modes_places.step list * Modes_places.step list option * int) list;
  mutable bound : (int * int) list;
  mutable spans : (int * (int * int)) list;
  cut : (int, unit) Hashtbl.t;
  jumps : (int, unit) Hashtbl.t;
  mutable steps : (int * int) list;
  mutable ranges : (int * int * int) list;
  mutable ticks : int;
  mutable joined : (int * int) list;
  mutable handed : write list;
}

type target = {
  head : int;
  mutable breaks : int list;
  mutable continues : int list;
}

type calls = {
  consumed : callee -> int list;
  may_store : Types.ty -> Types.ty list -> bool;
  cow : Types.ty -> bool;
}

type how = Out | Kept

type into = {
  leaves : how option;
  held_by : holder option;
  result : holder option;
  pattern : pattern option;
  lasts : extent;
  at : Modes_places.step list option;
}

type state = {
  calls : calls;
  flow : t;
  mutable frame : int;
  mutable frames : int;
  mutable tick : int;
  mutable blocks : int list;
  mutable block_count : int;
  mutable passed :
    (Hir.var * Modes_places.step list * point * holder * expr) list;
  mutable targets : target list;
}

let holders = function Bound (vs, _) -> vs | Place v -> [ v ] | Until _ -> []

let read lasts =
  {
    leaves = None;
    held_by = None;
    result = None;
    pattern = None;
    lasts;
    at = Some [];
  }

let leaving how = { (read Rest) with leaves = Some how }

(* What holds a value made where [into] says, such as a literal or a
   closure. *)
let keeper into =
  match (into.held_by, into.result, into.leaves) with
  | Some h, _, _ | None, Some h, _ -> h
  | None, None, Some Out -> Until Rest
  | None, None, _ -> Until into.lasts

let point st =
  st.tick <- st.tick + 1;
  { tick = st.tick; blocks = st.blocks }

let fresh_block st =
  st.block_count <- st.block_count + 1;
  st.block_count

(* The paths that execution may take (modes.shared-writes): a tick goes on to
   the next one unless it is cut, and to where its steps go. *)
let step st a b =
  if not (Hashtbl.mem st.flow.jumps a) then
    st.flow.steps <- (a, b) :: st.flow.steps

let meet ?(jumps = []) st froms =
  let p = point st in
  Hashtbl.replace st.flow.cut (p.tick - 1) ();
  List.iter (fun a -> step st a p.tick) froms;
  List.iter (fun a -> st.flow.steps <- (a, p.tick) :: st.flow.steps) jumps;
  p.tick

let jump st =
  let p = point st in
  Hashtbl.replace st.flow.cut p.tick ();
  Hashtbl.replace st.flow.jumps p.tick ();
  p.tick

let bind_at st vars =
  let p = point st in
  List.iter
    (fun (v : Hir.var) -> st.flow.bound <- (v.id, p.tick) :: st.flow.bound)
    vars

(* modes.shared-when-names: each pair of names of one [when] whose values have
   the same type. *)
let join_names st (names : (expr * Hir.var) list) =
  let rec pairs = function
    | [] -> ()
    | ((x : expr), (v : Hir.var)) :: rest ->
        List.iter
          (fun ((y : expr), (w : Hir.var)) ->
            if Types.zonk y.ty = Types.zonk x.ty then
              st.flow.joined <- (v.id, w.id) :: st.flow.joined)
          rest;
        pairs rest
  in
  pairs names

let spanning st id f =
  let first = st.tick + 1 in
  let r = f () in
  st.flow.spans <- (id, (first, st.tick)) :: st.flow.spans;
  r

let declare st (v : Hir.var) kind scope =
  Hashtbl.replace st.flow.decls v.id { var = v; kind; frame = st.frame; scope }

(* The declaration of a binding of the frame being walked. *)
let own st (v : Hir.var) =
  Option.bind (Hashtbl.find_opt st.flow.decls v.id) (fun d ->
      if d.frame = st.frame then Some d else None)

let copy ?(at = None) st binding path made holder stored =
  st.flow.copies <-
    { binding; path; made; came = made.tick; holder; stored; at; wide = false }
    :: st.flow.copies

let write ?(replaces = false) st (place : expr) =
  match Modes_places.place place with
  | Some { root; path } ->
      st.flow.writes <-
        { target = root.id; wpath = path; at = point st; place; replaces }
        :: st.flow.writes
  | None -> ()

(* The parts of the place at [path] that a pattern binds, each with the
   variable that binds it and its type. A variant's payload is a part of the
   variant that no place names apart. *)
let rec pattern_parts (p : pattern) path =
  let with_step step = path @ [ step ] in
  match p.pat with
  | P_bind v -> [ (path, v, p.pty) ]
  | P_record fields ->
      List.concat_map
        (fun (name, q) -> pattern_parts q (with_step (Modes_places.Field name)))
        fields
  | P_tuple ps ->
      List.concat
        (List.mapi
           (fun i q ->
             pattern_parts q (with_step (Modes_places.Field (string_of_int i))))
           ps)
  | P_variant (_, ps) | P_or ps ->
      List.concat_map (fun q -> pattern_parts q path) ps
  | P_list (ps, rest) -> (
      List.concat_map (fun q -> pattern_parts q (with_step Index)) ps
      @
      match rest with
      | Rest_bind v -> [ (with_step Index, v, p.pty) ]
      | Exact | Rest -> [])
  | P_wild | P_int _ | P_str _ | P_bool _ | P_const _ | P_error -> []

let binders p = List.map (fun (_, v, _) -> v) (pattern_parts p [])

let create calls =
  {
    calls;
    flow =
      {
        decls = Hashtbl.create 16;
        escapes = [];
        kept = [];
        held = [];
        copies = [];
        writes = [];
        assigned = [];
        reads = [];
        selves = [];
        bound = [];
        spans = [];
        cut = Hashtbl.create 16;
        jumps = Hashtbl.create 16;
        steps = [];
        ranges = [];
        ticks = 0;
        joined = [];
        handed = [];
      };
    frame = 0;
    frames = 0;
    tick = 0;
    blocks = [ 0 ];
    block_count = 0;
    passed = [];
    targets = [];
  }
