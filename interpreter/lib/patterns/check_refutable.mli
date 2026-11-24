(** Whether patterns can fail to match (patterns.irrefutable-positions), and the
    variants that names written without a module name in them
    (patterns.variants-by-type). *)

val matched_variant : Check_state.state -> Types.ty -> string -> Hir.item option
(** [matched_variant st ty name] is the variant [name] of [ty], when [ty] is
    known by its outermost constructor to be a variant type with a variant of
    that name (patterns.variants-by-type). *)

val irrefutable : Check_state.state -> ?ty:Types.ty -> Hir.pattern -> bool
(** Whether a pattern's form alone guarantees a match, given how many variants
    the types it names have (patterns.irrefutable-positions). A name written
    without a module names what checking the pattern found, or, before the
    pattern is checked, what it names as matched against [ty]
    (patterns.variants-by-type). *)

val require_irrefutable : Check_state.state -> Hir.pattern -> unit
(** Reports a pattern that can fail to match where it must not, once the pattern
    is checked. *)
