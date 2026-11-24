(** Calls: of functions, variants, members, methods and function values
    (expressions.arguments, traits.methods and traits.qualified-calls). *)

val arguments :
  Check_state.ctx ->
  Ast.loc ->
  (Types.mode * Types.ty) list ->
  Hir.arg list ->
  Tast.arg list
(** The arguments of a call, checked against its parameters' modes and types
    (expressions.arguments and expressions.inout-arguments;
    variadics.spread-expressions). *)

val give_up : Check_state.ctx -> Ast.loc -> Hir.arg list -> Tast.expr
(** A call that can't be checked, whose arguments are checked as the error type.
*)

val call : Check_state.ctx -> Ast.loc -> Hir.expr -> Hir.arg list -> Tast.expr
(** A call, whose arguments are checked against the callee's parameters
    (expressions.arguments and expressions.inout-arguments). A callee [x.m]
    calls the method [m] of [x], or a function that a field of [x] holds
    (traits.method-resolution). *)
