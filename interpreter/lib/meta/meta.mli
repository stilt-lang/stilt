(** The types of reflection (meta.std-meta, meta.shapes and meta.fresh-types):
    the native types of [std.meta], the cases of [Shape], and the fresh types
    that an arm or a loop body reads. *)

val home : string
(** [std.meta]. *)

val item : string -> Hir.item
(** The item of [std.meta] of this name. *)

val ty : string -> Types.ty list -> Types.ty
(** [ty name args] is the native type [name] of [std.meta], applied. *)

val shape : Hir.item
(** [Shape], the native variant type of meta.std-meta. *)

val is_meta : Hir.item -> bool
(** Whether an item is [std.meta]'s. *)

val cases : Types.ty -> (string * Types.ty) list
(** The cases of [Shape<t>], in order, each with its payload's type
    (meta.shapes), in which the fresh types [E], [K] and [V] are placeholders
    that {!freshen} replaces. *)

val placeholders : Hir.var list

(** {1 Fresh types (meta.fresh-types)} *)

val freshen : of_:Types.ty -> Types.ty -> Types.ty
(** [freshen ~of_ t] is [t] with each placeholder replaced by a fresh type of
    its own, part of the shape of [of_]. *)

val fresh : of_:Types.ty -> string -> Types.ty
(** A new fresh type, named as a diagnostic writes it, which is part of the
    shape of [of_]: a rigid type (polymorphism.rigid-types) with no bound. *)

val is_fresh : Hir.var -> bool

val origin : Hir.var -> Types.ty option
(** The type whose shape a fresh type is part of. *)

val mark : unit -> int
(** A mark of the fresh types made so far. *)

val since : int -> Hir.var -> bool
(** [since m v] tells whether [v] is a fresh type made after the mark [m]. *)

val fresh_in : int -> Types.ty -> Hir.var option
(** [fresh_in m t] is a fresh type made after the mark [m] that [t] holds. *)
