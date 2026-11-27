(** [match] in the Lean model's calculus: each arm with its guard, if it has one
    (patterns.guards), and each constant in a pattern a constant pattern of the
    model, or compared in the guard when its value is no literal
    (patterns.constants). *)

val guarded :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Types.ty ->
  Model_json.t ->
  Tast.arm list ->
  Model_json.t
(** The [match] of type [t] on the expression [scrutinee] of the arms, [expr]
    exporting their expressions. *)

val match_e :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  Tast.expr ->
  Tast.arm list ->
  Model_json.t
(** [match_e ~expr cx e x arms]: the [match] [e] on [x]. *)
