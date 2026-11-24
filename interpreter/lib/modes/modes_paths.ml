(* The paths that execution may take through a body (modes.shared-writes),
   searched breadth first from a tick, once for each tick, what ends them and
   the block they stay in. *)

open Modes_flow

type kill = Nothing | Whole of int | Covering of int * Modes_places.step list

type t = {
  next : int list array;
  assigned : (int, int * Modes_places.step list * int) Hashtbl.t;
  bound : (int, int) Hashtbl.t;
  cache : (int * kill * (int * int) option, bool array) Hashtbl.t;
}

let make (flow : Modes_flow.t) =
  let n = flow.ticks + 2 in
  let next = Array.make n [] in
  let add a b = if a >= 0 && a < n then next.(a) <- b :: next.(a) in
  for k = 0 to n - 2 do
    if not (Hashtbl.mem flow.cut k) then add k (k + 1)
  done;
  List.iter (fun (a, b) -> add a b) flow.steps;
  List.iter
    (fun (first, last, out) ->
      for k = max first 0 to last do
        add k out
      done)
    flow.ranges;
  let bound = Hashtbl.create 16 in
  List.iter (fun (v, tick) -> Hashtbl.add bound tick v) flow.bound;
  { next; assigned = Hashtbl.create 1; bound; cache = Hashtbl.create 16 }

let ended_by p assigned =
  let table = Hashtbl.create 16 in
  List.iter
    (fun (v, path, start, tick) -> Hashtbl.replace table tick (v, path, start))
    assigned;
  { p with assigned = table; cache = Hashtbl.create 16 }

let rec prefix a b =
  match (a, b) with
  | [], _ -> true
  | x :: a, y :: b -> x = y && prefix a b
  | _ :: _, [] -> false

(* Whether [kill] ends a path from [from] at the tick [k]. *)
let ends p kill from k =
  let binds v = List.mem v (Hashtbl.find_all p.bound k) in
  let assigns v covers =
    match Hashtbl.find_opt p.assigned k with
    | Some (u, path, start) ->
        u = v && covers path && not (start <= from && from <= k)
    | None -> false
  in
  match kill with
  | Nothing -> false
  | Whole v -> binds v || assigns v (fun path -> path = [])
  | Covering (v, at) -> binds v || assigns v (fun path -> prefix path at)

(* The ticks a path from [from] reaches: one may start outside [within] and
   enter it, but once inside it doesn't leave it. *)
let search p kill within from =
  let n = Array.length p.next in
  let seen = Array.make n false and before = Array.make n false in
  let inside k =
    match within with Some (lo, hi) -> lo <= k && k <= hi | None -> true
  in
  let queue = Queue.create () in
  let visit entered k =
    if k < n && not (ends p kill from k) then
      if inside k then (
        if not seen.(k) then (
          seen.(k) <- true;
          Queue.add (k, true) queue))
      else if (not entered) && not before.(k) then (
        before.(k) <- true;
        Queue.add (k, false) queue)
  in
  if from >= 0 && from < n then List.iter (visit (inside from)) p.next.(from);
  while not (Queue.is_empty queue) do
    let k, entered = Queue.pop queue in
    List.iter (visit entered) p.next.(k)
  done;
  seen

let reaches p ?(kill = Nothing) ?within a b =
  let key = (a, kill, within) in
  let seen =
    match Hashtbl.find_opt p.cache key with
    | Some seen -> seen
    | None ->
        let seen = search p kill within a in
        Hashtbl.replace p.cache key seen;
        seen
  in
  b >= 0 && b < Array.length seen && seen.(b)
