(** Type checking: phase 1 of errors.phases, after name resolution.

    Each body is checked on its own against the signatures in {!Env}, with
    inference local to the body, and elaborated into {!Tast}. A body is a
    function, a test, a doc example or a constant's initializer. Checking a body
    fits its effects to its declared row (effects.inference). *)

val check : Env.t -> Hir.program -> Tast.program * Diagnostic.t list
(** The elaborated program, and the type errors of every body in the program.
    Bodies of the standard library are checked too, and an error in one is a bug
    in it.

    @raise Failure if the standard library has errors. *)
