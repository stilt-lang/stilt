(** The stress suite: bodies built to stress inference (Goals, Workloads). Each
    program holds a function of one of four kinds, which [main] calls and
    prints: deep nesting, a long method chain, a large [match] or [if] tree, and
    literals whose type is known only at the end of the body. Like csmith
    programs, these are well-typed and terminating by construction. *)

val program : int -> string
(** The program of [seed]: its function, then [main], which prints what the
    function returns for a few arguments. The kinds take turns from one seed to
    the next, so a run of seeds holds as many of each. *)
