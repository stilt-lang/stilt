(** The prelude's structural impls of [Eq], [Ord] and [Show] at a type one of
    whose parts has an impl that the program writes (traits.structural-impls and
    traits.structural-calls): each a function that the export declares at each
    type it is used at, which calls the impls of the type's components from
    first to last. *)

val through_impls : Model_types.cx -> Ast.binary -> Types.ty -> bool
(** Whether the operator on values of the type calls an impl that the program
    writes, at the type or at a part of it. *)

val binary :
  Model_types.cx ->
  Ast.binary ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** The operator on such values, [==] through [Eq.eq] and the orderings through
    the [Ordering] of [Ord.compare] (traits.operators), its operands each
    evaluated once, in order. *)

val shown : Model_types.cx -> Types.ty -> Model_json.t -> Model_json.t
(** [shown cx t v]: the text of the value [v] of type [t] that a splice writes,
    by the impl of [Show] the program writes for [t], or as the prelude shows
    it, around the impls the program writes for its parts. *)

val structural_call :
  Model_types.cx ->
  Hir.item ->
  string ->
  Types.ty ->
  Model_json.t list ->
  Model_json.t
(** A call of [Eq.eq], [Ord.compare], [Show.show] or [Show.show_nested] at a
    [Self] whose impl the program doesn't write, its arguments exported. *)

val native_order : Model_types.cx -> Types.ty -> bool
(** Whether the order of [Ord.compare] at the type is the calculus's structural
    order. *)

val sorted_by_keys :
  Model_types.cx ->
  descending:bool ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [sorted_by_keys cx ~descending k t ks xs]: the stable sort of the list [xs]
    of [t] by its keys [ks] of [k], by [Ord.compare] at [k] (std.lists). *)
