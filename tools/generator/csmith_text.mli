(** Text beyond ASCII in a csmith program's [main], made from a stream of its
    own, so that the rest of the program is the one the same seed makes without
    it: strings of accented Latin, Greek, CJK, combining marks, emoji and
    characters outside the Basic Multilingual Plane, their lengths, slices on
    boundaries, characters, bytes and code points, searches, splits and
    replacements, comparisons, padding and format specs, the case mappings and
    classes of [std.text] (std.text), and strings made from code points and from
    bytes, valid or not (std.code-points). Nothing here can panic. *)

val wanted : int -> bool
(** Whether the program made from [seed] uses such text, from a stream of its
    own, so that it names [std.text] in a [use]. *)

val uses : Context.program -> int -> Code.line list list * Code.line list
(** The items the text of the program made from [seed] needs, two functions that
    walk a string's characters and bytes, and the lines of [main] that print
    what the methods and functions give. They make names from a copy of the
    program, so that the tests made after them are those of the same seed
    without them. *)
