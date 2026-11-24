(** Value parameters that a call can find
    (generics.value-parameters-determined). *)

val check :
  Resolve_context.ctx ->
  Hir.generic list ->
  Ast.fn_decl ->
  Hir.param list * Hir.ty option ->
  unit
(** Reports E0346 at each value parameter of [generics] that appears in none of
    the types of the parameters of the function [f], each read as written and as
    resolved, and not in its result type, outside every row. A parameter written
    in a type that has the error type stands there, since no diagnostic arises
    from the error type (errors.error-type). *)
