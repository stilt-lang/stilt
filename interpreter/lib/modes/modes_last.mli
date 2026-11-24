(** Last uses of bindings (facts.last-use), which in-place updates and lost
    reuse read. *)

type t
(** The last uses of a body's bindings. *)

val compute : Tast.block -> t
(** A use of a binding is its last use when no use of the binding follows it in
    source order and it isn't inside a loop that the binding's declaration is
    outside of. A use inside a closure literal counts as a use at the literal.
    Parameters are declared outside every loop. *)

val is_last : t -> Tast.expr -> bool
(** Whether an expression, a [Local] of the body, is the last use of its
    binding. *)
