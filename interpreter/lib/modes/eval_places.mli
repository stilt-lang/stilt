(** Places (expressions.places; values.assignment-order and
    values.compound-assignment-order): reading and writing the part of a
    variable's value that a place names, through the indexes of lists and maps
    (std.lists and std.maps), and through writable views
    (projections.places-through-views). *)

(** A part of a place (expressions.places): a field, a tuple's element, or an
    index into a container of the type, at the location of the index expression.
*)
type step = Value.step =
  | At_field of string
  | At_elem of int
  | At_key of Value.value * Types.ty * Ast.loc

type place = int * step list
(** A place of a frame (modes.places): its variable, by its id, and the steps
    into its value. *)

val frame_of : Eval_state.frame -> Value.window -> Eval_state.frame
(** The frame whose place a window writes, as the frame given for panics. *)

type _ Effect.t +=
  | Yield : Eval_state.frame * place -> unit Effect.t
        (** A projection handing its caller a place of its frame, which the
            caller's access reads or changes before the projection resumes
            (projections.yield and projections.when-projection-runs). *)

exception Access_raised of int * Value.value
(** A raise in the caller's access of a yielded place, on its way out of the
    projection numbered, which doesn't resume; no [catch] in it handles the
    error (projections.raising-during-access). *)

val index :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.value ->
  Value.value ->
  Value.value
(** [index t fr loc ty c k] is [c[k]], for a list, a map or a writable view [c]
    of type [ty]. It panics at [loc] if the list or the view has no such index,
    or the map no such key and no default. *)

val read : Eval_state.t -> Eval_state.frame -> place -> Value.value
(** The value of a place. *)

val returning : (unit -> unit) -> (unit -> Value.value) -> Value.value
(** [returning finish body] runs a body, which ends by returning or raising,
    then [finish]. *)

val store : Eval_state.t -> Eval_state.frame -> place -> Value.value -> unit
(** Sets the value of a place, building the variable's new value. Storing at a
    map's key inserts it (std.maps); storing through a writable view writes the
    place it views (projections.places-through-views). *)
