(** Shared values, tasks, scopes and the parallel calls of std.par as the Lean
    model's calculus writes them, in the program's sequential run
    (tasks.sequential-run): a shared value is a cell of the world, a handle
    names it, a [when] holds the cells it names, tasks, scopes and lazy values
    are forms of the calculus, and [std.par] calls. *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
  place : Tast.expr -> Model_json.t;
}

val when_ :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  (Tast.expr * Hir.var) list ->
  Tast.block ->
  Model_json.t
(** A [when] (shared.when). *)

val member_call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  string ->
  Tast.arg list ->
  Model_json.t
(** A call of [Shared.new], [Task.await] or [Scope.spawn]. *)

val lazy_call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t
(** A call of [Lazy.new] or [Lazy.get] (polymorphism.lazy-values). *)

val owns : Hir.item -> bool
(** Whether a type's functions are of std.sync or std.task. *)

val std_call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  Tast.arg list ->
  Model_json.t
(** A call of a function of std.task or std.par. *)
