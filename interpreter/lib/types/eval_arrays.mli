(** The natives of [std.array] (generics.arrays): [fill], [from_list] and [map].
*)

val native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [native t fr loc name targs args] calls the native of [std.array] named
    [name], whose concrete type arguments [targs] give the array's size, on its
    arguments. [map] calls its closure from [loc]. A negative size panics with
    [bounds], through {!Fault.Panic}. *)
