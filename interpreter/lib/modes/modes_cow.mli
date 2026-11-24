(** Recursive types (facts.allocation) and copy-on-write types
    (modes.copy-on-write-types), which the implicit effects and the modes read.
*)

val recursive : Env.t -> Hir.item -> bool
(** Whether a type's declaration names it again, directly or through the
    declarations of the types it names, type arguments and the parameter, result
    and error types of function types included (facts.allocation). *)

val is_cow : Env.t -> Types.ty -> bool
(** Whether a type is copy-on-write: [str], [List<T>], [Map<K, V>], a function
    type, a recursive type, or a record, tuple or variant type with a field,
    element or payload of one (modes.copy-on-write-types). A type parameter
    counts as one, since it may stand for one. *)

val may_store : Env.t -> Types.ty -> Types.ty list -> bool
(** Whether a call may store an argument of the first type in a value of one of
    the others, the types of its result and of its [inout] arguments: a part of
    the argument's value of a copy-on-write type may be a part of theirs
    (modes.call-stores). *)
