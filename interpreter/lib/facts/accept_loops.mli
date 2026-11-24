(** Counting loops and shrinking recursion (facts.counting-loops and
    facts.shrinking-recursion), and what each needs when it doesn't hold
    (facts.closest-rule). *)

val counting : Accept_rules.cx -> Accept_walk.looped -> (unit, string) result
(** Whether a [while] is a counting loop, or what the counting loop needs, as
    E0204 says it; a [loop] needs a comparison. *)

val shrinks :
  Accept_rules.cx -> (int * Hir.var) list -> Accept_rules.verdict option
(** Whether the body's self-calls shrink, at one of the [let] parameters of
    integer types given with their places, or what shrinking recursion needs;
    none for a body with no self-call. *)
