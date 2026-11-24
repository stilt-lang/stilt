(** Panics raised by the operations that the evaluator builds on, before they
    know where in the program they happened (effects.panic-kinds and
    effects.panicking-operations). *)

exception Panic of string * string
(** A panic of a kind of effects.panic-kinds, with its detail
    (program.panic-report). *)

val panic : string -> ('a, unit, string, 'b) format4 -> 'a
(** [panic kind fmt …] raises {!Panic} with the kind and the formatted detail.
*)
