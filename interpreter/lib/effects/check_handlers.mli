(** Effects and handlers: performances, handler literals and [resume]
    (handlers.performing-operation, handlers.handler-literals, handlers.with and
    handlers.resuming). *)

val perform_op :
  Check_state.ctx ->
  Ast.loc ->
  Hir.expr ->
  Hir.item ->
  Hir.name ->
  Hir.arg list ->
  Tast.expr
(** [perform_op ctx loc callee eff op args] performs the operation [op] of
    [eff], which [callee] names: its effect, with the type arguments that the
    rows around it give, or new variables, and its own row
    (handlers.performing-operation). *)

val operation_value :
  Check_state.ctx -> Ast.loc -> Hir.item -> Hir.name -> Tast.expr
(** E0311 at an operation named without a call, which is no value
    (handlers.performing-operation). *)

val handler_lit :
  Check_state.ctx -> Types.ty option -> Ast.loc -> Hir.handler_lit -> Tast.expr
(** A handler literal, which implements each operation of its effect once with
    the effect's types (E0511), and none of [async] (E0511, tasks.async). Its
    bodies perform their operations' rows, and its type's row holds [io] and its
    own effect, which they perform on the handler outside it; anything else is
    E0502 (handlers.handler-literals and handlers.handler-types). *)

val resume_expr : Check_state.ctx -> Ast.loc -> Hir.expr option -> Tast.expr
(** [resume(v)], in an operation's body of a handler that takes control, and
    E0513 anywhere else (handlers.resuming and
    handlers.resume-outside-operation). *)
