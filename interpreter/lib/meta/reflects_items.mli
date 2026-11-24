(** The items that may reflect (meta.reflects): their type parameters, and what
    each call or name of one gives them. *)

val params : Env.t -> Implicit_names.key -> Env.bounds * Hir.var list
(** The type parameters of an item, with their bounds, and those whose
    instantiation its callers can't see: a trait method's own, and a trait's
    [Self] in its default methods (meta.unseen-instantiations). *)

val target :
  Env.t ->
  Tast.callee ->
  Types.ty list ->
  (Implicit_names.key * (Hir.var * Types.ty) list) option
(** What calling or naming a callee with type arguments gives the type
    parameters of the item it reaches, when it reaches one: a method called
    through a bound reaches none. *)

val met :
  Env.t ->
  Env.bound list ->
  Types.ty ->
  (Implicit_names.key * (Hir.var * Types.ty) list) list
(** The methods of the impls with which a type meets bounds, each with what the
    type gives the impl's own type parameters, which are checked where the bound
    is met (meta.unseen-instantiations). *)

val name : Implicit_names.key -> string
(** The item as a message names it. *)
