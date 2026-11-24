(** Shrinking a failing case (tests.shrinking and tests.shrink-candidates): each
    value's candidates, in order, and the search that replaces a value with the
    first candidate whose run fails in the same way, until no candidate does or
    1,000 runs. *)

val candidates :
  Prop_gen.insert -> Prop_types.graph -> int -> Value.value -> Value.value Seq.t
(** The candidates of a value of a node's type, each once, none identical to the
    value (tests.shrink-candidates). The sequence is read once. *)

val limit : int
(** The most runs of the closure that shrinking makes: 1,000. *)

type 'f shrunk = { values : Value.value list; failure : 'f; shrinks : int }
(** The counterexample, the failure of its run, and the number of values
    replaced. *)

val shrink :
  candidates:(int -> Value.value -> Value.value Seq.t) ->
  run:(Value.value list -> 'f option) ->
  same:('f -> 'f -> bool) ->
  Value.value list ->
  'f ->
  'f shrunk
(** [shrink ~candidates ~run ~same values failure] shrinks the values of a case
    whose run failed with [failure] (tests.shrinking). [candidates j v] gives
    the candidates of parameter [j]'s value [v], and [run] the failure of a run
    on some values, or [None] when it passes. *)
