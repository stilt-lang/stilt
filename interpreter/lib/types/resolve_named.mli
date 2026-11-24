(** Named types: a path with its arguments, applied to what the path names
    (declarations.type-arguments; traits.member-types, traits.constructor-traits
    and traits.constructor-parameters; variadics.packs, variadics.type-spreads
    and variadics.pack-inference; generics.value-arguments). *)

open Resolve_context

val check_public : ctx -> Hir.loc -> Hir.item -> entry -> unit
(** E0214 for a private item in a signature that other modules see
    (program.private-in-signatures). *)

val as_type : Resolve_paths.meaning -> Hir.loc -> Hir.ty option
(** The type that a meaning is, written at [loc], if it is one. *)

val plural : int -> string
(** [""] for 1, and ["s"] for every other number. *)

val arity_error : ctx -> Hir.loc -> Hir.name list -> int -> int -> Hir.ty_desc
(** [arity_error ctx loc path arity given] reports E0300: the type [path] takes
    [arity] arguments, not [given]. *)

val named :
  ctx ->
  ?misplaced:(Hir.name -> string -> unit) ->
  Hir.loc ->
  Hir.name list ->
  (Resolve_paths.meaning * Hir.name * Hir.name list -> Hir.ty list) ->
  Hir.ty_desc
(** [named ctx loc path resolve_args] is the type [path] names, applied to the
    arguments that [resolve_args] resolves once the head is walked: a type, or a
    member type (traits.member-types). [misplaced] reports a path that names
    something else, E0212 unless it is given. *)
