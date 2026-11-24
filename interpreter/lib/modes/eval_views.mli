(** The native items of [std.view]: views and iterators (views.std-view). A
    view's value is the part of its source that it views (views.what-view-is).
*)

val slice : Value.value -> int64 -> int64 -> Value.value
(** [slice v start stop] is the part of the string or list [v] from [start] up
    to [stop], as [slice] counts it (std.str and std.lists): it panics with
    [bounds] unless [0 <= start <= stop <= len], and, for a string, with
    [utf8-boundary] when an offset falls inside a UTF-8 sequence. A view of the
    part has this value (views.what-view-is and views.making-view). *)

val native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Tast.callee ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [native t fr loc callee targs args] calls a native item of [std.view], with
    its concrete type arguments, on its arguments' values. A consumer of an
    iterator runs its adapters' closures and its own callback from the call at
    [loc] (views.laziness and views.consumers). *)
