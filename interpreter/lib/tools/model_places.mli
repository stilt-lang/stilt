(** Places whose index expressions and keys are evaluated once, into
    temporaries, as a store that also reads its place needs
    (values.compound-assignment-order and values.inout-argument-order). *)

type store =
  | Path of Model_json.t
  | Through of (Model_json.t -> Model_json.t)
      (** How a value is stored into a place: an assignment to a path from a
          variable, or, for a place through a map's element, an expression built
          from the value. *)

val write : store -> Model_json.t -> Model_json.t
(** The store of a value. *)

val receiver :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  (string * Model_json.t * Model_json.t) list * store * Model_json.t
(** A place's temporaries' bindings, how a value is stored into it, and the
    expression that reads it. *)
