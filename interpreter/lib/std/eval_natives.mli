(** The native items of the standard library (program.prelude-functions). *)

val native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Tast.callee ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [native t fr loc callee targs args] calls a native item, with its concrete
    type arguments, on the values of its arguments. A method that changes its
    receiver leaves the receiver's new value in [args]. The natives of lists and
    maps call the program's code, through callbacks and the impls of map keys,
    from [loc]. A native's own panics raise {!Fault.Panic}, which the caller
    locates. *)
