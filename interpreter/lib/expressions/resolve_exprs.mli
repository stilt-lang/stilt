(** Expressions, blocks and statements (patterns.let-else). *)

open Resolve_context

val resolve_expr : ctx -> Ast.expr -> Hir.expr
(** In a path such as [Name.member], [Name] is a type when it can be
    (declarations.name-lookup). *)

val resolve_block : ctx -> Ast.block -> Hir.block
(** The variables that a statement binds are in scope after it, not in its value
    (expressions.scope). *)
