(** Deep recursion and large lists in a csmith program's [main], made from a
    stream of their own, so that the rest of the program is the one the same
    seed makes without them: recursive functions tens of thousands of calls
    deep, among them a pair that call each other and one that sums a chain of a
    recursive variant type, and lists of 10^5 elements, and sometimes 10^6, with
    their lengths, extremes, folds, sorts and checked, wrapping and saturating
    sums. The depths stay within a fifth of what the reference interpreter's
    stack holds for these bodies. *)

val wanted : int -> bool
(** Whether the program made from [seed] recurses deeply and builds large lists,
    from a stream of its own. *)

val uses : int -> Code.line list list * Code.line list
(** The items the program made from [seed] needs for them, the chain's type and
    the recursive functions, and the lines of [main] that call them and build
    the lists. Their names are fixed, and none is a name the rest of the program
    makes. *)
