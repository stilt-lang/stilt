(** The walk of a body's code (facts.acceptance-places), in the order the code
    is written, which records what the rules of acceptance read. *)

val run :
  Env.t ->
  constant:(Tast.expr -> Accept_code.num option) ->
  self:Implicit_names.key option ->
  [ `Block of Tast.block | `Expr of Tast.expr ] ->
  Accept_walk.t
(** Walks the code of a body, a function's block or a lone expression, whose
    self-calls are the calls of [self]. *)
