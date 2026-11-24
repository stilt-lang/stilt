(** Fixed-size arrays, value parameters and staging annotations
    (generics.value-parameters and generics.arrays, meta.staging-annotations) in
    a csmith program's [main], made from a stream of their own, so that the rest
    of the program is the one the same seed makes without them: arrays of every
    type of one level and sizes 0 to 6, copied and written after the copy,
    rotated through [inout], reversed and shown by generic functions over their
    size, read by [for], [comptime for] and list patterns, kept in lists and
    records and written through them, and made by [fill], [from_list] and [map],
    and rings of integers modulo a value parameter. Nothing they do can panic.
*)

val wanted : int -> bool
(** Whether the program made from [seed] uses arrays, from a stream of its own,
    so it names [std.array] in a [use]. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The items that the arrays of the program made from [seed] need, its generic
    functions and a record type for each round, and the lines of [main] that use
    them, in the scope of [main] after its own lines. They make their names from
    a copy of the program, so the tests made after them are those of the same
    seed without them. *)
