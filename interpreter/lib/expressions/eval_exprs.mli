(** The evaluation of expressions, statements, patterns and calls, a tree walk
    over the elaborated program. Control leaves a body through the exceptions of
    {!Eval_state} (values.left-to-right and expressions.statements). *)

val expr : Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value
(** The value of an expression, in the frame of the body that holds it. *)

val block : Eval_state.t -> Eval_state.frame -> Tast.block -> Value.value
(** Runs the statements of a block in order, and gives the value of the last one
    if it is an expression, or [()]. *)

val apply :
  ?places:(Eval_state.frame * Eval_places.place) list ->
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Eval_state.target ->
  Value.value array ->
  Value.value
(** [apply t fr loc target values] calls [target], from the body of [fr] at
    [loc], on the values of its arguments. The callee leaves the final values of
    its [inout] parameters in [values] (values.inout-arguments). [places] gives
    the caller's places of the [inout] arguments, in order, which a window the
    callee returns into one of them writes instead
    (projections.what-view-writes). *)
