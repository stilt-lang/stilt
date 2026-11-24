(** User-defined effects and their handlers (handlers.declaring-effect and
    handlers.with) in a csmith program, made from a stream of their own, so that
    the rest of the program is the one the same seed makes without them: one to
    three effects, functions that perform them directly, through [map]'s closure
    and through one another, some writing [inout] parameters before and after
    performing, and lines of [main] that install handlers around blocks that
    perform them, nested, in loops and inside a [when]. A handler answers with a
    value, or takes control and resumes once, never, or on one path only, then
    prints and transforms the block's value; its bodies may perform its own
    effect on the handler outside it. Every step prints, so that differential
    testing compares the order of the events and the values they leave. *)

val wanted : int -> bool
(** Whether the program made from [seed] uses effects, from a stream of its own.
*)

val shares : int -> bool
(** Whether the program made from [seed] uses effects and may install handlers
    inside a [when], so names [std.sync] in a [use]. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The items that the effects of the program made from [seed] need, its effects
    and the functions that perform them, and the lines of [main] that handle
    them, in the scope of [main] after its own lines, whose variables they never
    write. They make their names from a copy of the program, so the tests made
    after them are those of the same seed without them. *)
