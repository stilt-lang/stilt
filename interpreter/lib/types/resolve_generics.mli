(** The generics that declare type parameters and row variables, their bounds,
    and [where] clauses (effects.row-variables; traits.bounded-blocks;
    traits.bound-arguments, traits.member-types and traits.where and
    traits.constructor-parameters). *)

open Resolve_context

val declare :
  ctx ->
  (string * Hir.var) list ->
  string ->
  Hir.name ->
  Hir.var * (string * Hir.var) list
(** [declare ctx scope what n] declares a type parameter or row variable [n] in
    [scope], [what] naming it in errors. Of two with the same name, the first
    stays declared, and a function's generics can't reuse the names of its impl
    block's (traits.impl-blocks) or its trait's parameters
    (traits.trait-parameters). *)

val declare_value : ctx -> Hir.name -> Ast.ty -> ctx * Hir.type_param
(** [declare_value ctx n t] declares the value parameter [n: t]
    (generics.value-parameters), whose type is an integer type or [bool]
    (E0345), and whose name no other value parameter or row variable in scope
    has (E0208). *)

val declare_generics : ctx -> Ast.generic list -> ctx * Hir.generic list
(** Declares a function's generics, in the context of its signature, followed by
    the type parameters that its member types imply (traits.member-types). The
    context knows each one's kind and member types. *)

val declare_impl_generics :
  ctx -> Ast.type_param list -> ctx * Hir.type_param list
(** Declares an impl's type parameters and value parameters, followed by the
    type parameters that its member types imply. A constructor trait bounds none
    of them (traits.constructor-parameters). *)

val resolve_where :
  ctx ->
  Ast.where_ option ->
  Hir.type_param list ->
  Hir.type_param list * (Hir.ty * Hir.bound * Hir.loc) list
(** Adds the bounds of a [where] clause to the type parameters that its member
    types are, and gives the bounds it puts on other types, each with the place
    of its member type: one that a bound's argument fixes, or one of an inherent
    impl's parameter (traits.where). *)

val where_generics :
  ctx ->
  Ast.where_ option ->
  Hir.generic list ->
  Hir.generic list * (Hir.ty * Hir.bound * Hir.loc) list
(** A function's generics with what its [where] clause adds to them, and the
    bounds it puts on other types. *)
