(* Writable views (projections.writable-views, projections.what-view-writes and projections.places-through-views): windows into the part of a
   list that a place of a frame holds. A write through a window writes the
   place (Eval_places), so a window can't be told from the part it views
   while the law of exclusivity keeps every other access away (projections.what-view-writes); a
   read of a window reads the part. *)

open Value
open Eval_state
open Eval_places

(* The part a window views, as a value of its own: what a read of the window
   reads, and what a read-only view of a writable binding copies (projections.places-through-views). *)
let thaw t fr = function
  | Window w -> (
      match read t (frame_of fr w) (w.root, w.path) with
      | List xs -> List (Vec.sub xs w.start w.stop)
      | _ -> invalid_arg "Eval_windows.thaw")
  | v -> v

let int = function Int a -> a | _ -> invalid_arg "Eval_windows.int"

(* projections.writable-views: the bounds of a part of a list of [length] elements, which panic
   as [View.of] does (views.making-view). *)
let bounds fr loc ~length start stop =
  if not (0L <= start && start <= stop && stop <= Int64.of_int length) then
    panic fr loc "bounds"
      "the range %Ld..%Ld is out of bounds for a list of length %d" start stop
      length
  else (Int64.to_int start, Int64.to_int stop)

(* [view.into(inout xs, start, end)]: a window into the place [xs], in the
   frame [wfr]. *)
let into t fr loc (wfr, (root, path)) start stop =
  match read t wfr (root, path) with
  | List xs ->
      let start, stop =
        bounds fr loc ~length:(Vec.length xs) (int start) (int stop)
      in
      Window { locals = wfr.locals; root; path; start; stop }
  | _ -> invalid_arg "Eval_windows.into"

(* [view.part(inout v, start, end)]: a window into part of the window that
   the place [v] holds, with offsets counted from its start. *)
let part t fr loc (wfr, place) start stop =
  match read t wfr place with
  | Window w ->
      let start, stop =
        bounds fr loc ~length:(w.stop - w.start) (int start) (int stop)
      in
      Window { w with start = w.start + start; stop = w.start + stop }
  | _ -> invalid_arg "Eval_windows.part"

(* [view.split(inout xs, at, f)]: the two windows that [f] is called with,
   before and from [at]. *)
let halves t fr loc (wfr, (root, path)) at =
  match read t wfr (root, path) with
  | List xs ->
      let length = Vec.length xs in
      let at, _ = bounds fr loc ~length (int at) (int at) in
      let window start stop =
        Window { locals = wfr.locals; root; path; start; stop }
      in
      (window 0 at, window at length)
  | _ -> invalid_arg "Eval_windows.halves"

(* The natives of [std.view] that take the place of a list or a view
   [inout], and give a window into it, each place opened by [opened], and the
   closure of [split] called by [call] (projections.writable-views). *)
let native t fr loc ~opened ~call name args =
  let value = function
    | Either.Left v -> v
    | Right _ -> invalid_arg "Eval_windows.native"
  in
  match (name, args) with
  | "into", [ Either.Right xs; start; stop ] ->
      opened xs (fun access -> into t fr loc access (value start) (value stop))
  | "part", [ Either.Right v; start; stop ] ->
      opened v (fun access -> part t fr loc access (value start) (value stop))
  | "split", [ Either.Right xs; at; f ] ->
      opened xs (fun access ->
          let a, b = halves t fr loc access (value at) in
          call (value f) a b)
  | _ -> invalid_arg "Eval_windows.native"

(* The windows in a value that a call returns: the value itself, or the
   payload of [Some] (views.view-types). *)
let rec map_windows f = function
  | Window w -> f w
  | Variant (({ name = "Some"; _ } as item), [ v ]) ->
      Variant (item, [ map_windows f v ])
  | v -> v

(* projections.what-view-writes and projections.reaching-written-source: a window that a call returns into an [inout]
   parameter of the callee, whose frame ends with the call, writes the
   caller's argument instead, which the write-back of the parameter gives
   the value the callee left. [places] gives, for each parameter by its
   variable's id, the caller's frame and place. *)
let retarget ~(callee : frame) places v =
  map_windows
    (fun w ->
      if w.locals != callee.locals then Window w
      else
        match List.assoc_opt w.root places with
        | Some ((caller : frame), (root, path)) ->
            Window { w with locals = caller.locals; root; path = path @ w.path }
        | None -> Window w)
    v

(* projections.call-is-place: the windows of a value copied out of a place of
   the frame [pfr] yielded by a projection, [target], that write an [inout]
   parameter of the projection, given the caller's [accesses] for its
   arguments, the places among them those of the [inout] ones: each writes
   the caller's argument instead. *)
let copied ~(target : target) ~accesses pfr v =
  let places =
    List.filter_map
      (function Either.Left _ -> None | Either.Right access -> Some access)
      accesses
  in
  match target with
  | Body (f, _) ->
      let inouts =
        List.filter_map
          (fun (mode, (v : Hir.var)) ->
            if mode = Ast.Inout then Some v.id else None)
          f.params
      in
      if List.length inouts = List.length places then
        retarget ~callee:pfr (List.combine inouts places) v
      else v
  | Closure_body _ | Native_code _ | Structural _ | Variant_of _ -> v
