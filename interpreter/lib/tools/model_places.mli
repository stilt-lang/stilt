(** Places whose index expressions and keys are evaluated once, into
    temporaries, as a store that also reads its place needs
    (values.compound-assignment-order and values.inout-argument-order). *)

type store =
  | Path of Model_json.t
  | Through of (Model_json.t -> Model_json.t)
      (** How a value is stored into a place: an assignment to a path from a
          variable, or, for a place through a map's element, an expression built
          from the value. *)

val through : Model_types.writable -> string -> Model_json.t -> Model_json.t
(** [through w j i]: the index of [v[i]] through the writable binding [w], with
    [i] read into [j]: the index into its source, or [-1] when it lies outside
    the binding's part (projections.places-through-views). *)

val through_map : Tast.expr -> bool
(** Whether a place goes through a map's element (std.map-element-places). *)

val element_place : Model_types.cx -> Tast.expr -> bool
(** Whether an assignment to the place is the calculus's form of one through a
    map's element: through exactly one element of a map the calculus holds,
    followed by a field or an index. *)

val compound_place : Model_types.cx -> Tast.expr -> bool
(** Whether the calculus has [p op= e] at the place [p] as its form
    (values.compound-assignment-order): at a place that [p = e] stores, or at
    the last key of a map whose keys are the calculus's. *)

val write : store -> Model_json.t -> Model_json.t
(** The store of a value. *)

val receiver :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  (string * Model_json.t * Model_json.t) list * store * Model_json.t
(** A place's temporaries' bindings, how a value is stored into it, and the
    expression that reads it. *)
