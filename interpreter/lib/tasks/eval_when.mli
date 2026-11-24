(** [when] at run time (shared.when-order). *)

val run :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  expr:(Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value) ->
  (Tast.expr * Hir.var) list ->
  (unit -> Value.value) ->
  Value.value
(** [run t fr loc ~expr names block] runs [block] with each name's variable the
    place of the value its handle reaches, two names reaching one value being
    one place, and gives the block's value. Once the block ends, however it
    ends, each value holds what its place holds. A [when] on a value that a
    [when] whose block hasn't ended holds panics with [deadlock] at [loc]
    (shared.when-on-value-already-held). *)

val captured : Eval_state.frame -> Value.value Value.Imap.t
(** The copies of the variables in scope that a closure literal captures
    (expressions.capture), the names of the [when]s around it among them. *)

val computing_lazy : (unit -> Value.value) -> Value.value
(** Runs the computation of a [Lazy]'s value, during which a [when] panics with
    [deadlock] (polymorphism.lazy-waits-for-nothing). *)
