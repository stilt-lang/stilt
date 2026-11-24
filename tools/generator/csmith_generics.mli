(** A trait, its impls and generic functions bounded by it (traits.impl-blocks,
    traits.bounds), in a csmith program's [main], made from a stream of their
    own, so that the rest of the program is the one the same seed makes without
    them: a trait of one method, impls for two or three of the program's types,
    its records and variant types among them, whose bodies are drawn like any
    other code, and generic functions that call the method on a list and on two
    values, called at each type. *)

val wanted : int -> bool
(** Whether the program made from [seed] declares the trait, from a stream of
    its own. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The trait, its impls and the generic functions of the program made from
    [seed], and the lines of [main] that call them at each type, in the scope of
    [main] after its own lines. They make their names from a copy of the
    program, so the tests made after them are those of the same seed without
    them. *)
