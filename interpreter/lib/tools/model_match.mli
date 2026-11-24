(** [match] in the Lean model's calculus, whose arms have no guards: the arms of
    a [match] with guards written as arms without them (patterns.guards). *)

val guarded :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Types.ty ->
  Model_json.t ->
  Tast.arm list ->
  Model_json.t
(** The [match] of type [t] on the expression [scrutinee], which may be read
    once for each arm with a guard, of the arms, [expr] exporting their
    expressions. *)

val match_e :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  Tast.expr ->
  Tast.arm list ->
  Model_json.t
(** [match_e ~expr cx e x arms]: the [match] [e] on [x], read into a temporary
    when an arm has a guard. *)
