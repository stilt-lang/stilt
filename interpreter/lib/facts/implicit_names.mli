(** The items whose implicit effects an operation inherits, because it names
    them (facts.inference). *)

(** An item with implicit effects. *)
type key =
  | Function of Hir.item
  | Member of Hir.item * string
      (** A function of an inherent impl, by its type constructor and name. *)
  | Impl_method of Hir.item * Hir.item * string
      (** A method of a trait impl, by its trait, type constructor and name. *)
  | Default_method of Hir.item * string
      (** A default method of a trait, by its trait and name. *)
  | Built_in of Hir.item * string
      (** A method of a trait, by its trait and name, of an impl that no source
          declares: a primitive type's, or a structural one
          (traits.structural-impls and traits.built-in-impls). *)

val show_key : key -> string
(** The item as a message names it. *)

val method_names : Env.t -> Hir.item -> string -> Types.ty -> key list
(** [method_names env trait name ty]: the items that calling the method [name]
    of [trait] on a value of type [ty] names. *)

val key_names : Env.t -> Types.ty -> key list
(** The items that finding a key in a map of the type names: the key type's
    impls of [Eq] and [Hash] (std.finding-keys). *)

val callee_names : Env.t -> Tast.callee -> Types.ty list -> key list
(** The items that calling, or naming, a callee with type arguments names. *)

val callee_key : Env.t -> Tast.callee -> key option
(** The item that a call by name calls: a function, an inherent member, or the
    method of the impl for the type, its own or the trait's default. A method
    called through a bound calls none. *)

val signature : Env.t -> key -> Env.fn_sig option
(** The declared signature of a function, an inherent member, or the trait
    method of a built-in impl. *)
