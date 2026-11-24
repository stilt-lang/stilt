(** [with] (handlers.with and handlers.resuming). *)

val with_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.expr list ->
  Hir.block ->
  Tast.expr
(** [with h₁, h₂ { … }], which is [with h₁ { with h₂ { … } }]. Each handler must
    have a handler type (E0311). The block's effects reach the [with] without
    the handled effect, and the [with] performs them and its handler type's row.
    With [-> R], the block has type [R] (E0311), and so does the [with]. *)
