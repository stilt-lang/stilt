(** Csmith programs with planted mistakes, annotated with the diagnostic the the
    Reference requires for each. *)

val mutant : ?count:int -> int -> (string * string) list
(** The files of a program from [seed] with [count] planted mistakes, 1 by
    default, or one in each of its functions if it has fewer: each at the top of
    a different function, and annotated with the diagnostic the Reference
    requires for it (conformance.diagnostic-lines). The mistakes take turns, so
    that each kind is planted as often as the others. A program with macros
    ({!Csmith_macros}) is the directory [seed_N], whose first mistake is in a
    use of a macro or in its module of macros ({!Macro_mistakes}); any other is
    the file [seed_N.lt]. *)
