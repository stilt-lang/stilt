(** Whether a type implements a trait, through an impl the program writes or
    structurally (traits.method-resolution, traits.structural-impls and
    traits.floats; std.map-key-bounds and traits.hash-follows-written-eq).

    {!Env} exports [answer], [implements] and [has_impl], and documents them. *)

open Env_tables

type answer = Yes | No | Unknown

val implements : t -> bounds -> Types.ty -> Hir.item -> answer

val impl_subst :
  t -> bounds -> impl -> Types.ty list -> (Hir.var * Types.ty) list
(** [impl_subst env bounds impl args] applies [impl] to [args], the type
    arguments of its type constructor: it gives each of the impl's generics that
    its type names its argument, and each that a member type implies the
    argument that the impl of its bound gives (traits.trait-arguments and
    traits.member-types). *)

val trait_args : t -> bounds -> Types.ty -> Hir.item -> Types.ty list option
(** [trait_args env bounds ty trait] is the list of arguments that the impl of
    [trait] for [ty], or the bound of the type parameter [ty], gives the trait's
    parameters (traits.trait-arguments and traits.bound-arguments), if there is
    one. *)

val structural_impl : t -> Hir.item -> Hir.item -> bool
(** [structural_impl env item trait] tells whether the type constructor [item]
    has a structural impl of [trait]: whether its type would implement it with
    every type parameter implementing it (traits.structural-impls). *)

val has_impl : t -> Types.ty -> Hir.item -> bool
