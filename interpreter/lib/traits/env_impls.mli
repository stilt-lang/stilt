(** Impls and the rules they follow (traits.impl-blocks,
    traits.implementing-trait and traits.method-resolution): where they are
    written, their types and their members. An impl with an error adds no
    members, but the names it declares are known (see {!Env.in_broken_impl}). *)

open Env_tables

type impl_site = {
  site_module : Hir.module_;
  node : Hir.impl_decl Hir.node;
  generics : bounds;
  head : head;
}
(** An impl, with its module and what its type names. *)

and head =
  | Head of Hir.item  (** A valid type: this constructor, applied. *)
  | Broken of Hir.item option
      (** A type with an error, and its constructor if the error leaves it
          known. *)

val impl_sites : diagnostics -> Hir.program -> impl_site list
(** Every impl of the program, in the order of the program. An impl's type must
    be a type constructor applied to the impl's type parameters, each once
    (traits.impl-blocks and traits.implementing-trait). *)

val add_broken : t -> impl_site -> Hir.item option -> t
(** [add_broken env site owner] records the members of an impl with an error,
    for the type constructor [owner] if it is known. Their uses have the error
    type (errors.declarations-with-errors). *)

val add_inherent :
  diagnostics ->
  t ->
  impl_site ->
  Hir.item ->
  t * (member * Hir.module_ * Ast.loc) list
(** [add_inherent d env site owner] adds an inherent impl of the type
    constructor [owner], and returns its members with their modules and the
    positions of their names. An impl outside the type's home module adds no
    member (traits.impl-blocks). *)

val add_trait_impl :
  diagnostics -> t -> impl_site -> Hir.item -> Hir.item -> Hir.ty list -> t
(** [add_trait_impl d env site owner trait args] adds an impl of [trait] for the
    type constructor [owner], which gives the trait's parameters [args]
    (traits.trait-arguments), after every inherent impl. It must be in the home
    module of one of them, be the only one, hold the methods the trait declares
    with their signatures (traits.impl-signatures), and hide no inherent method
    (traits.name-clashes). *)

val check_structural_clashes :
  diagnostics -> t -> (member * Hir.module_ * Ast.loc) list -> unit
(** Reports each inherent method that shares a name with a method of a
    structural impl its type has, at the inherent method (traits.name-clashes).
*)
