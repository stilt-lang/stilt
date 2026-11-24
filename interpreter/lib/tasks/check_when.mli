(** [when] (shared.when). *)

val when_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  (Hir.expr * Hir.var) list ->
  Hir.block ->
  Tast.expr
(** [when a, b { … }]: each name must be a local binding or parameter of type
    [Shared<T>] (E0433), and stands in the block for its value's place, of type
    [T]. The [when] has the block's type. *)
