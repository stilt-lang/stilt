(** The rules of acceptance (facts.rules-of-acceptance): six shapes of code, a
    range loop, a guard, a divisor, a key, a counting loop and shrinking
    recursion, that decide what [without panic] and [without div] accept, each
    read from a body's text alone, a closure literal's apart. *)

type verdict = Accept_rules.verdict =
  | Proved of Accept_rules.rule
  | Unproved of string
      (** With what the closest rule needs, as E0204 says it
          (facts.closest-rule). *)

type t
(** The verdicts of a body. *)

val constants : Tast.program -> Tast.expr -> Accept_code.num option
(** The value of a constant written as an integer literal, with or without a [-]
    (facts.terms), for an expression that names one. *)

val body :
  Env.t ->
  constant:(Tast.expr -> Accept_code.num option) ->
  key:Implicit_names.key option ->
  params:(Ast.mode * Hir.var) list ->
  [ `Block of Tast.block | `Expr of Tast.expr ] ->
  t
(** The rules on the code of the item [key], whose signature gives its
    parameters' types. *)

val access : t -> Tast.expr -> verdict
(** The verdict of an index [b[k]]: an element of a list or an array, or a read
    of a map's key (facts.range-loops, facts.guards and facts.keys). *)

val division : t -> Tast.expr -> verdict
(** The verdict of a [/] or a [%], or of a compound assignment's, by its place
    (facts.divisors). *)

val loop : t -> Tast.expr -> verdict
(** Whether a [while] ends, and what a [while] or a [loop] needs
    (facts.counting-loops). *)

val shrinks : t -> bool
(** Whether the self-calls shrink, which holds of no self-call
    (facts.shrinking-recursion). *)

val recursion_note : t -> string option
(** What shrinking recursion needs of self-calls that don't shrink. *)
