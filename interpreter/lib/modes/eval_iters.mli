(** Running iterators (views.for-over-view, views.making-iterator,
    views.adapters, views.laziness and views.consumers). An iterator's value
    describes its source and adapters, and each reading of it starts from its
    first element, asking for one element at a time, which passes through the
    adapters from the source outward. *)

val iterate :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Value.iter ->
  (Value.value -> bool) ->
  unit
(** [iterate t fr loc it each] calls [each] on the iterator's elements in turn,
    asking for each only after [each] has run on the one before, until the
    iterator ends or [each] gives [false], as a [for] loop over it does
    (views.for-over-view). The adapters' closures are called from [loc]. *)

val consume :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Types.ty list ->
  Value.iter ->
  Value.value array ->
  Value.value
(** [consume t fr loc name targs it args] runs the consumer [name] of
    views.consumers on [it], with the type arguments of its call and the values
    of its arguments, the iterator's first. It reads only the elements it needs,
    in order, and calls its callback on each as it reads it. *)
