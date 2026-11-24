(** Unification of types, and of effect rows (effects.inference and
    effects.function-values). *)

(** What a row can't hold, of the effects fitted into it. *)
type problem =
  | Missing_io
  | Missing_raise of Types.ty
  | Raise_mismatch of Types.ty * Types.ty
  | Missing_var of Hir.var
  | Cyclic_raise of Types.ty
      (** A raise whose type would hold the row itself. *)
  | Missing_effect of Hir.item
  | Effect_mismatch of Hir.item * Types.ty list * Types.ty list
      (** An effect performed with other type arguments, then those the row
          holds (handlers.effects-in-rows). *)

val open_var : Types.row -> Types.row_var option

val unify_all : Types.ty list -> Types.ty list -> bool
(** The open row variable that ends a row, if it ends in one. *)

val numeric : Hir.item -> bool
(** Whether an item is a numeric type. *)

val float : Hir.item -> bool
(** Whether a type constructor is a float type of the prelude. *)

val unify : Types.ty -> Types.ty -> bool
(** Makes two types one, and tells whether they can be. Meeting the error type
    taints every variable on the other side, so that none is reported as unknown
    (errors.error-type). *)

val fit : ?handled:Types.handled -> Types.row -> Types.row -> problem list
(** [fit actual expected] makes the effects of [actual] part of [expected], now
    and as [actual] grows, and returns what [expected] can't hold
    (effects.missing-effects and effects.function-values). A raise that
    [handled] catches, as a [try … catch] does, must have its type, and doesn't
    reach [expected], and neither does the effect that a [with] handles, whose
    arguments must be the handler's (handlers.with). *)
