(** Procedural macros (macros.procedural-declarations and
    macros.procedural-uses) in a csmith program, made from streams of their own,
    so that the rest of the program is the one the same seed makes without them:
    the program imports a module of macros ({!Macro_module}) with [meta use],
    since a macro is used only from another module (macros.meta-use), and uses
    each of its macros, in [main] and in functions of their own, the pattern
    macros in the arms of matches and the type macros where a type stands, each
    giving a value that [main] prints. Each use's parts are code of its scope of
    the types its macro takes, and some are uses themselves, so that the
    expansion checks where the use stands (macros.running). Nothing a macro does
    raises or runs out of its limits, and nothing it expands panics. *)

val wanted : int -> bool
(** Whether the program made from [seed] uses macros, from a stream of its own:
    one in ten do. *)

val part : string -> string
(** [text] as a part of a use, parenthesized if a comma outside its brackets
    would split it (macros.parts). *)

val uses :
  Macro_kinds.t ->
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The functions that use the macros of [m] in the program made from [seed],
    and the lines of [main] that use them and call those functions, in the scope
    of [main] after its own lines, and print what each gives. They make their
    names from a copy of the program, so the tests made after them are those of
    the same seed without them. *)
