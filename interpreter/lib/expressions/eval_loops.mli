(** The evaluation of loops (expressions.loops) and of the iterables of [for]
    (expressions.for-iterables; views.for-over-view). *)

val repeat :
  block:(Eval_state.t -> Eval_state.frame -> Tast.block -> Value.value) ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.block ->
  (unit -> bool) ->
  unit
(** Runs a loop's body while [more ()] holds, until it breaks. *)

val turn :
  block:(Eval_state.t -> Eval_state.frame -> Tast.block -> Value.value) ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.block ->
  bool
(** Runs a loop's body once, and tells whether the loop goes on. *)

val iterate :
  expr:(Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value) ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.iterable ->
  (Value.value -> bool) ->
  unit
(** Runs [each] on the elements of an iterable in order, while it gives [true].
*)
