(** The natives of [std.par] (par.std-par), [std.sync] (shared.std-sync) and the
    scopes of [std.task] (tasks.scopes and tasks.scope-failure), as the
    sequential run that is a program's meaning runs them. *)

val tree : ('a -> 'a -> 'a) -> 'a list -> 'a
(** [tree combine xs] combines the elements of a non-empty list in the balanced
    tree of par.fold-tree: its first [n / 2] elements, then the rest. *)

val par_native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Value.value array ->
  Value.value
(** A function of [std.par], by name, on its arguments. *)

val sync_native : string -> Value.value array -> Value.value
(** A function of [Shared<T>], by name, on its arguments. *)

val scope_native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Value.value array ->
  Value.value
(** [task.scope] or [Scope.spawn], by name, on its arguments. *)
