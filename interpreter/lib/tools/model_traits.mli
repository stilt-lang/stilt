(** Operators and splices through the impls of the prelude's traits that a
    program writes (traits.operators and traits.structural-impls): each calls
    the impl's method, which the export declares as a function of its own. *)

val written :
  Model_types.cx -> Hir.item -> string -> Types.ty -> Model_types.target option
(** [written cx trait name t]: the method [name] of the impl of [trait] that the
    program writes, with code, for the head of [t], if it writes one. *)

val call_values :
  Model_types.cx ->
  Model_types.target ->
  Types.ty list ->
  Model_json.t list ->
  Types.ty ->
  Model_json.t
(** A call of a function with code on values already exported, of these types,
    evaluated in order, whose result has the last type. *)

val through_written : Model_types.cx -> Ast.binary -> Types.ty -> bool
(** Whether the operator on operands of this type calls a written impl's method:
    [==] and [!=] the [eq] of [Eq], the orderings the [compare] of [Ord]. *)

val operator :
  Model_types.cx ->
  Ast.binary ->
  Types.ty * Model_json.t ->
  Types.ty * Model_json.t ->
  Model_json.t
(** The operator through the written impl, on its operands' types and values. *)

val compare :
  Model_types.cx ->
  Tast.expr ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [compare cx e t x y]: the call [e], [x.compare(y)] at a type [t] whose [Ord]
    is structural, as the [Ordering] its structural order gives. *)

val composed :
  Model_types.cx -> int -> Types.ty -> (Model_json.t -> Model_json.t) option
(** [composed cx 0 t]: how [Show] writes a value of type [t] when a part of [t]
    has an impl of its own: a list, an option, a map or a tuple around parts
    that are shown by their own impl or structurally without strings, or [None]
    for any other. *)

val shown : Model_types.cx -> Types.ty -> Model_json.t -> Model_json.t
(** [shown cx t v]: the text of the value [v] of type [t] that a splice writes,
    by the impl of [Show] the program writes for [t], or as the prelude shows
    it, around the impls the program writes for its parts. *)

val structural_call :
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  string ->
  Types.ty ->
  Model_json.t list ->
  Model_json.t
(** A call of [Ord.compare], [Show.show] or [Eq.eq] through a structural impl at
    [Self], its arguments exported. *)

val composed_eq : Model_types.cx -> Types.ty -> bool
(** Whether [==] on a tuple or a record reaches a component's written [Eq]
    through the structural impl. *)

val composed_ord : Model_types.cx -> Types.ty -> bool
(** Whether [<] on a tuple or a record reaches a component's written [Ord]
    through the structural impl. *)

val tuple_eq :
  Model_types.cx ->
  Tast.expr ->
  Ast.binary ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [x == y] or [x != y], the expression [e], on a value that {!composed_eq}. *)

val composed_operator :
  Model_types.cx ->
  Tast.expr ->
  Ast.binary ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [x < y] and the other ordering operators, the expression [e], on a value
    that {!composed_ord}. *)

val composed_at : Model_types.cx -> Ast.binary -> Types.ty -> bool
(** Whether the operator on a value of the type is composed of its components'
    impls, {!composed_eq} or {!composed_ord}. *)

val composed_binary :
  Model_types.cx ->
  Tast.expr ->
  Ast.binary ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** The operator, the expression, on a value that {!composed_at}. *)
