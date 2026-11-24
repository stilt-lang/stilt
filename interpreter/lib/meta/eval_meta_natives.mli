(** The accessors of [std.meta], all native (meta.shape-accessors, meta.fields
    and meta.accessor-effects). *)

val native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  string ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [native t fr loc owner name targs args] runs the method [name] of the native
    type [owner] of [std.meta], whose impl's type arguments [targs] give the
    type that the shape is of first. *)
