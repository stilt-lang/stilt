(** A call with an [inout] argument through a map's element, [f(inout m[k])]:
    its value read into a fresh variable when the call starts, which the call
    takes [inout], and stored back with [m[k] = v] when it returns or raises
    (std.finding-keys and values.inout-argument-order). *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  place : Tast.expr -> Model_json.t;
  store : Tast.expr -> Tast.expr -> Model_json.t;
      (** [p = v], a map's element included. *)
}

val has_map_inout : Tast.arg list -> bool
(** Whether a call has an [inout] argument through a map's element. *)

val through_maps :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  raise:Types.ty option ->
  (Model_json.t list -> Model_json.t) ->
  Tast.arg list ->
  Model_json.t
(** The call [e] of these arguments, made by the function given the arguments
    passed; [raise] is the error the callee may raise. *)
