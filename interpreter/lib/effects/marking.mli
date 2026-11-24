(** Marking and handling: every call that can raise is inside a [try]
    (effects.marking), no [catch] can catch what a row variable raises
    (effects.catch-around-row-variables, as effects.catch-around-row-variables
    amends it), and every catch-all gives a reason or raises again
    (effects.catch-alls-need-reason). *)

val errors :
  file:string ->
  pairs:(Hir.var * Tast.label) list ->
  passed:(Ast.loc * Types.row * Tast.label) list ->
  Tast.block ->
  Diagnostic.t list
(** The calls of a body that can raise and that no [try] marks, and the calls
    inside a [catch]'s operand that can raise through a row variable an error
    type the [catch] doesn't expect. [pairs] are the row variables that the
    body's signature pairs with an error type. Also the uses that pass one of
    those variables on to a callee that pairs it with another error type, or an
    unpaired one to a callee that pairs it
    (effects.passing-to-paired-variables), as [passed] records them, and the
    calls inside a [with]'s block that perform through a row variable that the
    signature doesn't pair with the handled effect (E0516,
    handlers.with-pairing). *)

val warnings : file:string -> Tast.block -> Diagnostic.t list
(** The [try]s of a body that mark nothing, and its catch-alls with neither a
    reason nor a raise. *)

val raises : Types.row -> bool
(** Whether a row holds a [raise] label, after inference. *)

val raising_call : Tast.expr -> bool
(** Whether the expression is a call whose callee's row raises. *)

val handles_never : Tast.catch -> bool
(** Whether a [catch] handles [Never], because its operand raises nothing
    (effects.non-escaping-parameters). *)
