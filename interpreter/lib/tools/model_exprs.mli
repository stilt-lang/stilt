(** The expressions of a program as the Lean model's calculus writes them: a
    write to the output or a read of the input is an operation on the world. *)

val block : Model_types.cx -> Tast.block -> Model_json.t

val expr : Model_types.cx -> Tast.expr -> Model_json.t
(** An expression as the calculus writes it. *)
