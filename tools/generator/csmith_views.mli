(** Views (views.what-view-is) of the fields of records in a csmith program's
    [main], made from a stream of their own, so that the rest of the program is
    the one the same seed makes without them: views of a record's list, string
    and list of strings, and of a field of a record in a list in another record,
    and views of those views, read by index, [view.get], [for] and iterators,
    compared with each other and with copies of their parts, and passed to
    functions that return views of their parameters (views.across-calls); then
    writes through writable views of the fields, of a view and of [view.split]'s
    parts (projections.writable-views), read back beside a copy made before
    them. Every offset lies inside its source and on the boundary of a
    character, so nothing panics. *)

val wanted : int -> bool
(** Whether the program made from [seed] views fields, from a stream of its own,
    so that it names [std.view] in a [use]. *)

val uses :
  Context.program ->
  Context.scope ->
  int ->
  Code.line list list * Code.line list
(** The items the views of the program made from [seed] need, the two record
    types and the functions on views, and the lines of [main] that make and read
    them, in the scope of [main] after its own lines. They make names from a
    copy of the program, so that the tests made after them are those of the same
    seed without them. *)
