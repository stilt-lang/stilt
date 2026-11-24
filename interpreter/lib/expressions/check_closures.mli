(** Closures, and key paths, which stand for closures (expressions.key-paths).
*)

val key_path : Hir.expr -> bool
(** Whether an expression is a key path, such as [.name] or [.items[0]]. *)

val key_path_closure :
  Check_state.ctx -> Types.ty option -> Hir.expr -> Tast.expr
(** A key path, as the closure of one parameter that it means where a function
    type of one parameter is expected. *)

val closure :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.closure_param list ->
  Hir.expr ->
  Tast.expr
(** A closure, whose parameters and row the expected type gives where there is
    one. *)
