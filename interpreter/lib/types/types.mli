(** The types that the type checker works with ({!Types_core}), and the
    substitution of their parameters (types.inferred-per-body and
    types.infinite-types). *)

include module type of struct
  include Types_core
end

(** {1 Substitution} *)

val subst : (Hir.var * ty) list -> (Hir.var * row) list -> ty -> ty
(** Replaces type parameters and row parameters, by their [id]s. A pack is
    replaced by a tuple of its elements, which its spreads stand for one by one
    (variadics.type-spreads). *)

val subst_row : (Hir.var * ty) list -> (Hir.var * row) list -> row -> row
(** Each row parameter that the substitution replaces gives way to its
    replacement, which gains the row's labels. At most one of the replacements
    of one row may end in an open row. *)

val mentions_param : Hir.var list -> ty -> bool
(** Whether one of the type parameters occurs in the type, at any depth. *)

val instance : forall -> ty list -> ty
(** [instance p args] is the body of [p] with its type parameters replaced by
    [args], in order (polymorphism.instantiation). *)

val instance_bounds : forall -> ty list -> bound list list
(** The bounds of [p]'s type parameters, each with [args] in place of them. *)
