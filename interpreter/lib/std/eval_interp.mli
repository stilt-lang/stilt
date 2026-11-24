(** The evaluation of interpolated strings (lexical.interpolation and
    lexical.format-specs; std.width-fill-and-alignment). *)

val interpolated :
  expr:(Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value) ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.segment list ->
  Value.value
(** The string that the segments make, each splice shown with its format spec.
*)
