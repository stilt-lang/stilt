(* Locality and shared writes (modes.escaping, modes.not-escaping, modes.copies and modes.shared-writes), read from the
   flow of a body. *)

open Modes_flow

(* The bindings that aren't parameters and escape: by themselves, or when a
   closure literal that they hold escapes, with the bindings it captures
   (meta.fresh-types). *)
let escapes (flow : t) =
  let rec grow found =
    let next =
      List.fold_left
        (fun acc (hs, captured) ->
          if List.exists (fun h -> List.mem h acc) hs then
            List.filter (fun v -> not (List.mem v acc)) captured @ acc
          else acc)
        found flow.held
    in
    if List.length next = List.length found then found else grow next
  in
  grow (List.sort_uniq compare flow.escapes)

let held_ids h = List.map (fun (v : Hir.var) -> v.id) (holders h)

let rec prefix a b =
  match (a, b) with
  | [], _ -> true
  | x :: a, y :: b -> x = y && prefix a b
  | _ :: _, [] -> false

let drop n l = List.filteri (fun i _ -> i >= n) l

(* The copy [c] as the holder of [d], a later copy of a part of [c]'s holder,
   holds it: its path and its place there. The part holds the copy, or lies
   inside it and is a copy of a part of the copied binding; a part beside the
   copy holds none of it. A copy at no known place in its holder may be in
   any part. *)
let within (d : copy) (c : copy) =
  match c.at with
  | None -> Some (c.path, None)
  | Some inner when prefix d.path inner ->
      let rest = drop (List.length d.path) inner in
      Some (c.path, Option.map (fun outer -> outer @ rest) d.at)
  | Some inner when prefix inner d.path ->
      Some (c.path @ drop (List.length inner) d.path, d.at)
  | Some _ -> None

(* Every copy, with the copies of copies (modes.copies): a copy that a binding
   holds goes wherever a copy of that binding's part that holds it, made on a
   path after it, goes, and is a copy of the first binding there, held by what
   holds the later copy. A copy found again at another place inside its holder,
   or of a part inside a part it is a copy of already, is the same copy, so
   that copies passed around a cycle of bindings end; the copy found first may
   then hold any part below its path (modes.shared-writes). *)
let transitive paths (found : copy list) =
  let same (d : copy) (e : copy) =
    e.binding = d.binding && e.made = d.made && e.came = d.came
    && e.holder = d.holder && e.stored = d.stored && prefix e.path d.path
  in
  let wide = ref [] in
  let carried (c : copy) (d : copy) =
    d.made.tick <> c.came
    && Modes_paths.reaches paths c.came d.made.tick
    && not (List.mem c.binding (held_ids d.holder))
  in
  let derive (c : copy) (d : copy) =
    Option.map
      (fun (path, at) ->
        {
          c with
          came = d.made.tick;
          holder = d.holder;
          stored = d.stored;
          path;
          at;
        })
      (within d c)
  in
  let fresh all (d : copy) =
    match List.find_opt (same d) all with
    | Some e ->
        if e.path <> d.path || e.at <> d.at then wide := e :: !wide;
        false
    | None -> true
  in
  let rec grow all = function
    | [] -> all
    | c :: rest ->
        let derived =
          List.concat_map
            (fun h ->
              List.filter_map
                (fun d ->
                  if d.binding = h && carried c d then derive c d else None)
                found)
            (held_ids c.holder)
          |> List.filter (fresh all)
        in
        grow (all @ derived) (rest @ derived)
  in
  let all = grow found found in
  List.map
    (fun c -> if List.memq c !wide then { c with wide = true } else c)
    all

(* The ticks a copy lasts in, along a path from where it came into its holder
   (modes.copies): none past its expression, the rest of the function when
   what holds it escapes, or the block that holds the binding that holds it. *)
let region flow escaped c =
  let span = function
    | Here -> None
    | Rest -> Some None
    | Scope block -> Some (List.assoc_opt block flow.spans)
  in
  let escapes (v : Hir.var) = List.mem v.id escaped in
  match c.holder with
  | Bound (hs, _) when c.stored && List.exists escapes hs -> Some None
  | Bound (_, ext) | Until ext -> span ext
  | Place root when escapes root -> Some None
  | Place root -> (
      match Hashtbl.find_opt flow.decls root.id with
      | Some d -> span d.scope
      | None -> Some None)

let overlap a b =
  let fields p =
    List.filter_map
      (function Modes_places.Field f -> Some f | Index -> None)
      p
  in
  let rec prefix a b =
    match (a, b) with
    | [], _ -> true
    | x :: a, y :: b -> x = y && prefix a b
    | _, [] -> false
  in
  let fa = fields a and fb = fields b in
  prefix fa fb || prefix fb fa

(* Whether an assignment of the whole of [v] whose value holds a part of [v]'s
   own value, among [own], is on a path from the tick [from] to the tick
   [until]: after it, a copy made before it counts as a copy of every part of
   [v] (modes.shared-writes). *)
let reshaped paths own v from until =
  List.exists
    (fun (u, _, _, tick) ->
      u = v
      && Modes_paths.reaches paths from tick
      && Modes_paths.reaches paths tick until)
    own

(* modes.shared-writes: a copy shares the part a write modifies when it copies
   the part and a path from where it was made reaches the write, while it lasts
   and with no assignment of the whole binding, and no binding of it anew, on
   the way. *)
let sharing paths flow escaped own (c : copy) (w : write) =
  let kill = Modes_paths.Whole w.target in
  c.binding = w.target
  && (overlap c.path w.wpath
     || reshaped paths own w.target c.made.tick w.at.tick)
  &&
  match region flow escaped c with
  | None -> false
  | Some within ->
      (c.made.tick = c.came
      || Modes_paths.reaches paths ~kill c.made.tick c.came)
      && Modes_paths.reaches paths ~kill ?within c.came w.at.tick

(* modes.shared-writes: whether an assignment of the whole of a binding [u]
   holds a part of [u]'s own value, read from [u] or from another binding that
   holds a copy of it, so that it is no assignment of the whole for the rule. *)
let holds_own paths flow copies (u, path, start, tick) =
  let within k = k >= start && k <= tick in
  let holds_copy r made =
    r = u
    || List.exists
         (fun (c : copy) ->
           c.binding = u
           && List.mem r (held_ids c.holder)
           && c.came <> made
           && Modes_paths.reaches paths c.came made)
         copies
  in
  path = []
  && (List.exists (fun (v, _, _, k) -> v = u && within k) flow.selves
     || List.exists
          (fun (c : copy) ->
            List.mem u (held_ids c.holder)
            && within c.made.tick
            && holds_copy c.binding c.made.tick)
          flow.copies)

(* Whether [v] might still read the value it had at [from] after the write
   [w]: a path from [from] reaches [w] with no assignment of [v]'s whole, and
   no binding of it anew, on the way, and goes on to a read of [v], or [v] is
   read when the body of [w] ends: an [inout] parameter of that body, which
   goes back to its caller, or a binding of an enclosing body that it
   captures, which the closure's next call reads; or [w] is a modification
   that starts a call, which reads [v] after it when [v] is the root of one of
   its [inout] arguments. *)
let read_after paths flow v ~from (w : write) =
  let kill = Modes_paths.Whole v in
  let frame id =
    Option.map (fun (d : decl) -> d.frame) (Hashtbl.find_opt flow.decls id)
  in
  let at_end =
    match Hashtbl.find_opt flow.decls v with
    | Some { kind = Param Ast.Inout; frame = f; _ } -> Some f = frame w.target
    | Some { frame = f; _ } -> Some f <> frame w.target
    | None -> false
  in
  let by_the_call (u, first, read) =
    u = v && first <= w.at.tick && w.at.tick < read
  in
  Modes_paths.reaches paths ~kill from w.at.tick
  && (at_end
     || List.exists by_the_call flow.inout_reads
     || List.exists
          (fun (u, (p : point)) ->
            u = v && Modes_paths.reaches paths ~kill w.at.tick p.tick)
          flow.reads)

(* The part of the copied binding that [w] modifies, when it reaches inside
   the copy [c] that its binding holds: a path from where the copy came there
   reaches [w] with no assignment to the place that holds it, and no binding of
   the binding anew, on the way. After an assignment of the whole binding that
   holds a part of its own value, or when copies of copies may have given the
   binding any part, the write may reach anywhere inside the copy. *)
let reached paths own (c : copy) (w : write) =
  match c.at with
  | Some at
    when c.binding <> w.target
         && List.mem w.target (held_ids c.holder)
         && Modes_paths.reaches paths
              ~kill:(Covering (w.target, at))
              c.came w.at.tick ->
      if c.wide || reshaped paths own w.target c.came w.at.tick then Some c.path
      else if
        prefix at w.wpath
        && not (w.replaces && List.length at >= List.length w.wpath)
      then Some (c.path @ List.filteri (fun i _ -> i >= List.length at) w.wpath)
      else None
  | _ -> None

(* modes.shared-writes: a write that reaches inside a copy of another binding's
   part that its binding holds, as its value or at a place inside it, while
   that binding, or another binding that holds a copy of the part, might still
   read it. A copy made on a path through an assignment of the whole copied
   binding that holds a part of its own value, before or after the copy the
   write reaches, may be of any part of it. *)
let mirrored paths flow own c w =
  match reached paths own c w with
  | None -> None
  | Some _ when read_after paths flow c.binding ~from:c.made.tick w ->
      Some c.binding
  | Some part ->
      let any (d : copy) =
        reshaped paths own c.binding c.made.tick d.made.tick
        || reshaped paths own c.binding d.made.tick c.made.tick
      in
      List.find_map
        (fun d ->
          if
            d.binding = c.binding
            && (not (List.mem w.target (held_ids d.holder)))
            && (overlap d.path part || any d)
          then
            List.find_opt
              (fun h -> read_after paths flow h ~from:d.made.tick w)
              (held_ids d.holder)
          else None)
        flow.copies

type shared = {
  place : Tast.expr;
  binding : Hir.var option;
  holder : Hir.var option;
}

(* modes.handles: a call of [Shared.new] is shared when the binding whose value
   it is given might still read it after the call: a parameter, which its
   caller reads, or a binding read on a path from the call. *)
let var flow id =
  Option.map (fun (d : decl) -> d.var) (Hashtbl.find_opt flow.decls id)

let handed paths flow =
  List.filter_map
    (fun (w : write) ->
      let parameter =
        match Hashtbl.find_opt flow.decls w.target with
        | Some { kind = Param _; _ } -> true
        | _ -> false
      in
      let read_on =
        List.exists
          (fun (u, (p : point)) ->
            u = w.target
            && Modes_paths.reaches paths ~kill:(Modes_paths.Whole u) w.at.tick
                 p.tick)
          flow.reads
      in
      if parameter || read_on then
        Some { place = w.place; binding = var flow w.target; holder = None }
      else None)
    (List.rev flow.handed)

let shared (flow : t) =
  let escaped = escapes flow in
  let paths = Modes_paths.make flow in
  let copies = transitive paths flow.copies in
  let own, assigned =
    List.partition (holds_own paths flow copies) flow.assigned
  in
  let paths = Modes_paths.ended_by paths assigned in
  let var = var flow in
  List.filter_map
    (fun w ->
      match Hashtbl.find_opt flow.decls w.target with
      | Some { kind = Var | Param Ast.Inout; _ } -> (
          match
            List.find_opt (fun c -> sharing paths flow escaped own c w) copies
          with
          | Some c ->
              Some
                {
                  place = w.place;
                  binding = var w.target;
                  holder = List.nth_opt (holders c.holder) 0;
                }
          | None ->
              List.find_map (fun c -> mirrored paths flow own c w) copies
              |> Option.map (fun id ->
                  { place = w.place; binding = var w.target; holder = var id }))
      | _ -> None)
    (List.rev flow.writes)
  @ handed paths flow
