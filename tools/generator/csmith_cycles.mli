(** Cycles through [Shared<T>] handles (cycles.through-shared-values) in a
    csmith program's [main], made from a stream of their own, so that the rest
    of the program is the one the same seed makes without them: rings of one to
    four handles, walked through [when]s past their start, sometimes written
    through one of them first, and a function that makes up to 3,000 two-handle
    rings and lets each go, so that the compiler's runtime collects them as the
    program runs. *)

val wanted : int -> bool
(** Whether the program made from [seed] links handles, from a stream of its
    own, so it names [std.sync] in a [use]. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The items that the cycles of the program made from [seed] need, the type of
    a ring's links and the functions that walk and spin rings, and the lines of
    [main] that make and walk them, in the scope of [main] after its own lines.
    They make their names from a copy of the program, so the tests made after
    them are those of the same seed without them. *)
