(** The parsers that a cursor calls (macros.cursor): the longest run of tokens
    that is a whole expression, pattern or type of the language's own grammar,
    read with no terminator at its top level (macros.part-forms), and stops
    before a [,], a [;] or the end. *)

val parse :
  Hir.code ->
  Macro_values.token array ->
  int ->
  Macro_values.span ->
  (Macro_values.code * int, Macro_values.error) result
(** The code of the longest run of [items] from [at] that parses whole as [form]
    and stops before a [,], a [;] or the end, and the position after it; or the
    error at [at], reported at [close] when no token is left
    (macros.part-forms). *)
