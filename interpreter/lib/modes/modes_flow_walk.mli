(** The walk of a body in source order that finds its flow (modes.escaping and
    modes.not-escaping, 6 and 7). *)

val walk :
  Modes_flow.calls ->
  params:(Ast.mode * Hir.var) list ->
  Tast.block ->
  Modes_flow.t
(** The flow of a body whose function has the parameters [params], its value
    returned. *)
