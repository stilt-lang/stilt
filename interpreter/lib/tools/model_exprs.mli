(** The expressions of a program as the Lean model's calculus writes them: a
    write to the output or a read of the input is an operation on the world. *)

val block : Model_types.cx -> Tast.block -> Model_json.t

val result_block : Model_types.cx -> string -> Tast.block -> Model_json.t
(** [result_block cx p body]: the body of a function whose result writes its
    parameter [p], its result given as its part's start and end
    (projections.results-that-write). *)

val expr : Model_types.cx -> Tast.expr -> Model_json.t
(** An expression as the calculus writes it. *)
