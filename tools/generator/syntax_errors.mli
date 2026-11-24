(** Programs with planted syntax errors, made by editing the tokens of other
    programs, which check that a parser reports each file's first syntax error
    where the reference interpreter does (goal
    compiler-checks-like-interpreter). Most edits break the program somewhere;
    some leave it valid, which checks the trees too. *)

val mutant : string array -> int -> string
(** The program of [seed]: an edit of one of [sources], which the seed picks.
    The edit deletes, duplicates or swaps one to three tokens, or inserts or
    replaces them with other tokens or with bits of text that are lexical errors
    or doc comments. *)

val sources : string list -> string array
(** The texts of the [.lt] files under [dirs], sorted by path, outside any
    [_pending] directory, but for those whose runs can't be compared with
    another's: those that draw from the system's randomness or read a clock. *)
