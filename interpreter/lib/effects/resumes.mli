(** Resuming at most once (handlers.resume-at-most-once). *)

val errors : file:string -> Tast.block -> Diagnostic.t list
(** E0514 at each [resume] of an operation's body, of a handler that takes
    control, that may run after another on one path, or that a loop or a closure
    literal holds, in source order. *)
