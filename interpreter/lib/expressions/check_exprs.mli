(** Expressions (types.inferred-per-body and types.expected-types). *)

val infer : Check_state.ctx -> Types.ty option -> Hir.expr -> Tast.expr
(** The checked form of an expression, with its type. Where an expected type is
    given, the expression is checked against it, in the forms that can use it,
    and the caller requires the result to fit it. Every context holds this
    function, as [Check_state.ctx.infer]. *)
