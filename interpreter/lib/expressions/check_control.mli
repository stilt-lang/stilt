(** Branches and loops: [if], [if let], [match], [try … catch], [loop], [while]
    and [for]. Each takes the expected type, if any, and the position of the
    expression (expressions.if, expressions.if-let, expressions.match,
    expressions.loops and expressions.break-and-continue). *)

val list_element : Types.ty -> Types.ty option
(** The element type of a list type, which a view of the list yields when a
    [for] runs over it or an index reads it (views.functions-of-views and
    views.for-over-view). *)

val if_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.expr ->
  Hir.block ->
  Hir.expr option ->
  Tast.expr

val if_let_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.pattern ->
  Hir.expr ->
  Hir.block ->
  Hir.expr option ->
  Tast.expr
(** An [if let], whose pattern may be refutable, typed as an [if]
    (expressions.if-let). *)

val match_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.expr ->
  Hir.arm list ->
  Tast.expr

val try_expr :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.expr ->
  Hir.arm list option ->
  Tast.expr
(** A [try], whose arms, if it has any, handle its operand's raise
    (effects.marking). *)

val loop_expr : Check_state.ctx -> Ast.loc -> Hir.block -> Tast.expr
(** A [loop], of type [()] if a [break] exits it, or else [Never]
    (expressions.loop-types). *)

val while_expr :
  Check_state.ctx -> Ast.loc -> Hir.expr -> Hir.block -> Tast.expr

val for_expr :
  Check_state.ctx ->
  Ast.loc ->
  Hir.pattern ->
  Hir.iterable ->
  Hir.block ->
  Tast.expr
(** A [for] over a list, a map or a range. *)
