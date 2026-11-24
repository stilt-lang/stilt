(** The parameters that pass their arguments' effects through, and where they
    escape (effects.escaping-parameters and effects.no-escape). *)

val errors :
  Env.t ->
  file:string ->
  through:Hir.var list ->
  Tast.block ->
  Diagnostic.t list
(** The errors of a body whose non-escaping parameters are [through]: one for
    each that the body keeps, at its first use in source order that isn't a call
    of it, or an argument given to a non-escaping parameter of what a call
    names, directly or in a closure literal. *)
