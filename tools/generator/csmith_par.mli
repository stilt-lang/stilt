(** Calls of [std.par] (par.std-par) at the end of a csmith program's [main],
    made from a stream of their own, so that the rest of the program is the one
    the same seed makes without them: [map], [each], [both] and [fold] over
    lists usually long enough to run on several threads, folds of floats whose
    bits the tree of par.fold-tree fixes, and, rarely and last, a call whose
    closure may panic on several elements, of which par.panics reports the
    first. *)

val wanted : int -> bool
(** Whether the program made from [seed] calls [std.par], from a stream of its
    own, so it names [std.par] in a [use]. *)

val calls : Context.program -> Context.scope -> int -> Code.line list
(** The lines that make the calls of the program made from [seed], in the scope
    of [main] after its own lines, and print what each gives. They declare
    nothing in the program, and make their names from a copy of it, so the tests
    made after them are those of the same seed without them. *)
