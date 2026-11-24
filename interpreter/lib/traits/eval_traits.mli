(** The prelude traits, which run the program's impls or the structural ones
    (traits.prelude-traits, traits.structural-impls and traits.floats), and what
    builds on them: the keys of maps, and the binary operators. The primitive
    types have only their structural impls, since no module can write others for
    them.

    Each operation takes the state, the frame of the body that runs it, and the
    location at which its panics are reported. *)

val equal :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.value ->
  Value.value ->
  bool
(** [Eq.eq]. *)

val order :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.value ->
  Value.value ->
  int
(** [Ord.compare], as a negative number, zero or a positive number. *)

val hash :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.value ->
  int64
(** [Hash.hash]. *)

val show :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Types.ty ->
  Value.value ->
  string
(** [show t fr loc name ty v] calls [Show.show] or [Show.show_nested], as [name]
    says. *)

val structural :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Types.ty ->
  Value.value array ->
  Value.value
(** [structural t fr loc name ty values] runs the structural impl of the method
    [name] of a prelude trait, for a type without a written impl
    (traits.structural-impls). *)

(** {1 Maps} *)

val lookup :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.dict ->
  Value.value ->
  (int * Value.value) option
(** [lookup t fr loc kty d k] finds the key [k], of type [kty], by hashing it
    once, then comparing it with each key of the same hash, in insertion order
    (std.finding-keys). It gives the entry's stamp and value. *)

val insert :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Types.ty ->
  Value.dict ->
  Value.value ->
  Value.value ->
  Value.dict
(** [insert t fr loc kty d k v] maps the key [k], of type [kty], to [v]. An
    entry that the map holds keeps its key and its position, and a new one goes
    at the end. *)

(** {1 Operators} *)

val binary :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Ast.binary ->
  static:Types.ty ->
  right:Types.ty ->
  Types.ty ->
  Value.value ->
  Value.value ->
  Value.value
(** [binary t fr loc op ~static ~right ty a b] is [a op b], where [static] is
    the left operand's type as the program writes it and [ty] that type with the
    body's type arguments, and [right] the right operand's type with them, which
    only a shift's amount doesn't share (numbers.shift-amounts). It takes no
    [&&] or [||], whose second operand doesn't always run. *)
