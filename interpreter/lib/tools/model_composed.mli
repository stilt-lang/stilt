(** The prelude's structural impls of [Eq], [Ord], [Hash] and [Show] at a type
    one of whose parts has an impl that the program writes
    (traits.structural-impls and traits.structural-calls): each a function that
    the export declares at each type it is used at, which calls the impls of the
    type's components from first to last. *)

val native : Model_types.cx -> Model_code.kind -> Types.ty -> bool
(** Whether the calculus's operations give the trait's function at the type,
    every impl in it structural. *)

val at :
  Model_types.cx ->
  Model_code.kind ->
  Types.ty ->
  Model_json.t list ->
  Model_json.t
(** [at cx k t xs]: the trait's function at [t] on the operands [xs], each
    evaluated once, in order: the impl's that the program writes for [t]'s head,
    the calculus's operations, or the structural impl's function at [t]. *)
