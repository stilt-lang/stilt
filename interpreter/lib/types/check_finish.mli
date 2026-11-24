(** The end of a body: the rules whose answer needs every type of the body,
    decided once inference is done (types.undecided-types and
    types.range-bounds). *)

val finish : Check_state.state -> unit
(** Gives the types that are still open their defaults, and then reports, in
    this order: unused values, and [if]s without [else] that have one
    (expressions.unused-values and expressions.if); literals out of their types'
    ranges (numbers.integer-literals and numbers.float-literals and
    numbers.negative-literals); float patterns (patterns.floats); operators on
    types that don't support them (numbers.no-implicit-conversions); missing
    trait impls (traits.unsatisfied-bounds; traits.bound-reported-once); format
    specs that don't apply (std.invalid-specs); and, when nothing else is wrong,
    the types that inference didn't decide (types.undecided-types). *)
