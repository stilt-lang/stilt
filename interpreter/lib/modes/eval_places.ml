(* Places (expressions.places; values.assignment-order and values.compound-assignment-order): reading and writing the part of a
   variable's value that a place names, through the indexes of lists and maps
   (std.lists and std.maps). *)

open Value
open Eval_state
open Eval_types
open Eval_traits
module T = Types

(* A part of a place (expressions.places): a field, a tuple's element, or an index into a
   container of the type, at the location of the index expression. *)
type step = Value.step =
  | At_field of string
  | At_elem of int
  | At_key of value * T.ty * Ast.loc

(* A place of a frame (modes.places): its variable and its steps. *)
type place = int * step list

(* The window of a writable view (projections.places-through-views), as the frame whose place
   it writes. *)
let frame_of fr (w : window) = { fr with locals = w.locals }

type _ Effect.t +=
  | Yield : Eval_state.frame * place -> unit Effect.t
        (** A projection handing its caller a place (projections.yield). *)

exception Access_raised of int * value
(** A raise in the caller's access of a yielded place, on its way out of the
    projection numbered, which doesn't resume
    (projections.raising-during-access). *)

let list_index fr loc xs = function
  | Int i when i >= 0L && i < Int64.of_int (Vec.length xs) -> Int64.to_int i
  | Int i ->
      panic fr loc "bounds" "index %Ld is out of bounds for a list of length %d"
        i (Vec.length xs)
  | _ -> invalid_arg "Eval_places.list_index"

(* An index into the part a window views, as an index into its list
   (projections.places-through-views). *)
let window_index fr loc (w : window) = function
  | Int i when i >= 0L && i < Int64.of_int (w.stop - w.start) ->
      Int (Int64.add i (Int64.of_int w.start))
  | Int i ->
      panic fr loc "bounds" "index %Ld is out of bounds for a view of length %d"
        i (w.stop - w.start)
  | _ -> invalid_arg "Eval_places.window_index"

(* [c[k]] (std.lists and std.maps). *)
let rec index t fr loc ty container k =
  match container with
  | List xs -> Vec.get xs (list_index fr loc xs k)
  | Window w ->
      let k = window_index fr loc w k in
      index t fr loc ty (read t (frame_of fr w) (w.root, w.path)) k
  | Map d -> (
      match lookup t fr loc (fst (key_value_types ty)) d k with
      | Some (_, v) -> v
      | None -> (
          match d.default with
          | Some v -> v
          | None ->
              panic fr loc "missing-key"
                "the key isn't in the map, which has no default"))
  | _ -> invalid_arg "Eval_places.index"

and read t fr (root, steps) =
  let step v = function
    | At_field f -> (
        match v with
        | Record (_, fields) -> List.assoc f fields
        | _ -> invalid_arg "Eval_places.read")
    | At_elem i -> (
        match v with
        | Tuple xs -> List.nth xs i
        | _ -> invalid_arg "Eval_places.read")
    | At_key (k, ty, loc) -> index t fr loc ty v k
  in
  List.fold_left step (Hashtbl.find fr.locals root) steps

let rec store t fr (root, steps) v =
  let rec update current = function
    | [] -> v
    | At_field f :: rest -> (
        match current with
        | Record (item, fields) ->
            let field (g, x) = if g = f then (g, update x rest) else (g, x) in
            Record (item, List.map field fields)
        | _ -> invalid_arg "Eval_places.store")
    | At_elem i :: rest -> (
        match current with
        | Tuple xs ->
            Tuple (List.mapi (fun j x -> if j = i then update x rest else x) xs)
        | _ -> invalid_arg "Eval_places.store")
    | At_key (k, ty, loc) :: rest -> (
        match current with
        | List xs ->
            let i = list_index fr loc xs k in
            List (Vec.set xs i (update (Vec.get xs i) rest))
        | Window w ->
            (* A write through a writable view writes the place it views
               (projections.places-through-views). *)
            let k = window_index fr loc w k in
            let wfr = frame_of fr w in
            let elem = index t wfr loc ty (read t wfr (w.root, w.path)) k in
            store t wfr
              (w.root, w.path @ [ At_key (k, ty, loc) ])
              (update elem rest);
            current
        | Map d ->
            (* [m[k] = v] is [insert] (std.maps). *)
            let inner =
              match rest with
              | [] -> v
              | _ -> update (index t fr loc ty current k) rest
            in
            Map (insert t fr loc (fst (key_value_types ty)) d k inner)
        | _ -> invalid_arg "Eval_places.store")
  in
  Hashtbl.replace fr.locals root (update (Hashtbl.find fr.locals root) steps)

(* Runs a body, which ends by returning, raising or being abandoned by a
   handler (handlers.call-that-handler-ends), then [finish]. *)
let returning finish body =
  match body () with
  | v ->
      finish ();
      v
  | exception Return v ->
      finish ();
      v
  | exception ((Raised _ | Access_raised _ | Abandoned) as ended) ->
      finish ();
      raise ended
