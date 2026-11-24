(** Exhaustiveness and reachability of the arms of [match] and [catch]
    (patterns.algorithm, patterns.non-exhaustive-matches and
    patterns.unreachable-arms; effects.catch). *)

val check :
  Env.t -> file:string -> Tast.block -> Diagnostic.t list * Diagnostic.t list
(** The errors for the [match]es and [catch]es of a body whose arms don't cover
    every value, each with a missing pattern in its message, and the warnings
    for the arms that can never match. *)
