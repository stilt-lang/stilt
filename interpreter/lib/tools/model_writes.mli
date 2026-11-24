(** Views that write in the Lean model's calculus: a writable binding holds a
    copy of the part it writes, written back into its source when its scope ends
    (projections.writable-views and projections.what-view-writes). *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

val owns : Hir.item -> bool
(** Whether the function is [view.into], [view.part] or [view.split]. *)

val binding :
  callbacks ->
  Model_types.cx ->
  Hir.var ->
  Tast.expr ->
  Tast.block ->
  Model_json.t
(** A writable [var] binding of a view, its initializer, and the rest of its
    block. *)

val call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  Tast.arg list ->
  Model_json.t
(** A call of [view.into] or [view.part] that no writable binding holds, which
    reads, or of [view.split]. *)
