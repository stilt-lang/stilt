(** The evaluation of patterns (patterns.pattern-forms), with [expr] evaluating
    guards and constant patterns. *)

type expr = Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value

val arms :
  expr:expr ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.arm list ->
  Value.value ->
  Value.value
(** The value of the body of the first arm that matches a value, with the arm's
    bindings made. *)

val pattern :
  expr:expr ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.pattern ->
  Value.value ->
  bool
(** Whether a pattern matches a value, making its bindings in the frame. *)
