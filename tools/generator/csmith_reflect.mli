(** Reflection (meta.shapes and meta.reflects) in a csmith program's [main],
    made from a stream of its own, so that the rest of the program is the one
    the same seed makes without it: values of random types written through every
    case of their shape, their fields and cases iterated by [comptime for], made
    again by [fields.build] and [make], named, and tested against a trait that a
    random half of the program's types implement. Nothing it does can panic. *)

val wanted : int -> bool
(** Whether the program made from [seed] uses reflection, from a stream of its
    own, so it names [std.meta] in a [use]. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The items that the reflection of the program made from [seed] needs, its
    generic functions, its trait and the impls of it, and the lines of [main]
    that use them, in the scope of [main] after its own lines. They make their
    names from a copy of the program, so the tests made after them are those of
    the same seed without them. *)
