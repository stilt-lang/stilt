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

val holds_str : Model_types.cx -> Types.ty -> bool
(** Whether a type holds a string, which a structural [Show] writes quoted when
    it is nested and bare when it isn't (std.show-output). *)
