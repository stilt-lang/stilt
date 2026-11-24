(** Written types, effect rows and bounds (declarations.type-arguments;
    effects.rows; traits.impl-blocks; traits.bound-arguments,
    traits.member-types and traits.constructor-traits). A private item can't
    appear in a signature that other modules see
    (program.private-in-signatures). *)

open Resolve_context

val implicit_effects : string list
(** The implicit effects, which no row writes (facts.implicit-effects). *)

val effect_names : string list
(** [io] and the implicit effects, which no row variable is named. *)

val plural : int -> string
(** [""] for 1, and ["s"] for every other number. *)

val mentions : ?rows:bool -> Hir.var -> Hir.ty -> bool
(** [mentions v t] tells whether the parameter [v] appears in [t], counting the
    raises of its rows unless [rows] is false (polymorphism.function-types;
    generics.value-parameters-determined). *)

val has_error : Hir.ty -> bool
(** Whether a type has the error type anywhere in it. *)

val resolve_ty : ?poly:bool -> ctx -> Ast.ty -> Hir.ty
(** A written type. A constructor parameter takes its arity's number of
    arguments, as [Self] does in a constructor trait (traits.constructor-traits
    and traits.constructor-parameters), and [C.Item] is a member type of the
    type parameter [C] (traits.member-types). A polymorphic function type may be
    the type itself only where [poly] says it is a parameter's, a field's or a
    payload's, and else is E0340 and the error type (polymorphism.placement).
    Each of its type parameters appears in its parameters or its result (E0339),
    and writing one makes the module advanced . An anonymous record type names
    each field once (E0316, records.anonymous-types); an open one is E0341 and
    the error type, since only a parameter's type is open
    (records.open-parameter-types). A pack is written only in a spread (E0343),
    which names exactly one pack and stands in no other spread
    (variadics.type-spreads). *)

val record_fields : ctx -> Ast.field_decl list -> Hir.field_decl list
(** The fields of an anonymous record type or a record bound, each named once
    (E0316), which makes the module advanced (records.anonymous-types,
    records.record-bounds and records.advanced-tier). *)

val record_bound : ctx -> Ast.ty -> Hir.field_decl list
(** The fields of a record bound, written as a record type that ends with [..]
    (E0341, records.record-bounds). *)

val resolve_row : ctx -> Ast.row -> Hir.row
(** An effect row, which holds each kind of element at most once and never an
    implicit effect (effects.rows, and facts.implicit-effects). *)

val constructor : ctx -> int -> Ast.ty -> Hir.ty
(** [constructor ctx arity t] is the type of an impl of a constructor trait of
    [arity]: a type constructor of that arity, written without its arguments
    (traits.constructor-impls). Any other is E0337 and the error type. *)

val record_ty : ctx -> Hir.name list -> Hir.ty
(** The type a struct literal or a record pattern names
    (declarations.name-lookup). *)

val as_type : Resolve_paths.meaning -> Hir.loc -> Hir.ty option
(** The type that a meaning is, written at [loc], if it is one. *)

(** {1 Bounds} *)

type resolved_bound = {
  bound : Hir.bound;
  implied : Hir.type_param list;
      (** The type parameters that its member types name, for a bound written
          without the trait's arguments (traits.member-types). *)
  arity : int;
      (** Its trait's arity as a constructor trait (traits.constructor-traits).
      *)
  params : string list;  (** Its trait's parameters. *)
  at : Hir.loc;
}

val resolve_bound : ctx -> ?implied_by:string -> Ast.bound -> resolved_bound
(** A bound, with all the trait's arguments or none (traits.bound-arguments).
    With none, [implied_by] names the type parameter whose member types are the
    arguments: [C] gives [C.Item]. Without [implied_by], as for an impl's trait
    (traits.bound-arguments), every argument must be written (E0300). A record
    bound here is E0341: its fields are {!record_bound}'s, where a type
    parameter has them (records.record-bounds). *)
