(** Patterns: their types (patterns.pattern-types). *)

val holds_float : Env.t -> Types.ty -> bool
(** Whether a value of the type can hold a float, which a pattern can't match
    (patterns.floats). *)

val pattern : Check_state.ctx -> Hir.pattern -> Types.ty -> Tast.pattern
(** A pattern that matches values of a type, binding its variables. *)
