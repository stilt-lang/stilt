(** Blocks, and the statements in them: bindings and assignments
    (expressions.statements, expressions.block-value and patterns.let-else). *)

val option_fallback :
  Check_state.ctx -> Ast.loc -> Hir.expr -> Tast.expr -> Hir.expr -> Tast.expr
(** [option_fallback ctx loc a x b] is the [Option] fallback [a else b] at
    [loc], once [a] is inferred as [x] (expressions.option-fallback). *)

val block_expr :
  Check_state.ctx ->
  at:Ast.loc ->
  Types.ty option ->
  Hir.block ->
  Tast.block * Types.ty
(** A block and its type. Checked against an expected type, a block has that
    type: its final expression is checked against it, and a block without one
    has type [()], which must fit it, as reported at [at]. *)

val loop_body : Check_state.ctx -> at:Ast.loc -> Hir.block -> Tast.block
(** A loop's body, whose value is discarded, so that its last expression
    statement, like every other, must have type [()] or [Never]
    (expressions.statements). *)
