(** The bodies the export writes of closures, of [for] loops and of functions
    whose result writes, given the export of expressions and blocks. *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
  assign : Ast.binary option -> Tast.expr -> Tast.expr -> Model_json.t;
  writing : Model_writes.callbacks;
}

val for_loop :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Tast.pattern ->
  Tast.iterable ->
  Tast.block ->
  Model_json.t
(** A [for] over a list, or over the list of the integers a range yields
    (expressions.range-iteration), each element matched against the loop's
    pattern. *)

val closure :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Tast.pattern list ->
  Tast.expr ->
  Model_json.t
(** A closure literal, its parameters of a view type writable
    (projections.writable-bindings). *)

val result_block :
  callbacks -> Model_types.cx -> string -> Tast.block -> Model_json.t
(** [result_block cb cx p body]: the body of a function whose result writes its
    parameter [p], its result given as its part's start and end
    (projections.results-that-write). *)
