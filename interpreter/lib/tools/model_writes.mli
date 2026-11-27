(** Views that write in the Lean model's calculus: a writable binding and the
    rest of its block are a call of a closure literal that takes the binding's
    source [inout], so copy-in, copy-out writes the part back into the source
    when the scope ends, and in place the binding writes the source's storage at
    once (projections.writable-views and projections.what-view-writes). *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

val part_of : Model_types.writable -> Model_json.t
(** What a writable binding reads: the view of its part, from its start to its
    end in its source's parameter. *)

val owns : Hir.item -> bool
(** Whether the function is [view.into], [view.part] or [view.split]. *)

val result_writes : (Ast.mode * Types.ty) list -> Types.ty -> int option
(** The position of the one parameter whose argument a function's result writes,
    when the result is a view of a list and that parameter is the one source
    passed [inout]: the calculus writes such a function as one that gives the
    part's start and end in that argument (projections.results-that-write). *)

val target_writes : Model_types.cx -> Model_types.target -> int option
(** {!result_writes} of the function's signature. *)

val offsets_ty : Types.ty
(** The type of a part's start and end, [(i64, i64)]. *)

val call_result : callbacks -> Model_types.cx -> Tast.expr -> Model_json.t
(** A call of a function whose result writes, read: the view of its part in the
    argument it writes, read after the call. *)

val offsets : callbacks -> Model_types.cx -> string -> Tast.expr -> Model_json.t
(** [offsets cb cx p e]: the result [e] of a function whose result writes its
    parameter [p], given as its part's start and end. *)

val yielded :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  (Model_json.t list -> Model_json.t) ->
  Model_json.t
(** [yielded cb cx init call]: [yield init] of a view that writes its source,
    [call] called with the arguments that pass it to a writable parameter. *)

val binding :
  callbacks ->
  Model_types.cx ->
  Hir.var ->
  Tast.expr ->
  Tast.block ->
  Model_json.t
(** A writable [var] binding of a view, its initializer, and the rest of its
    block, as the call of a closure that takes the view's source [inout]. *)

val call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  Tast.arg list ->
  Model_json.t
(** A call of [view.into] or [view.part] that no writable binding holds, which
    reads, or of [view.split]. *)

val makes : Model_types.cx -> Tast.expr -> bool
(** Whether an expression makes a view that writes its source: [view.into],
    [view.part], or a call of a function whose result writes. *)
