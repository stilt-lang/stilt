(** Indexes, divisions and keys (facts.range-loops, facts.guards, facts.divisors
    and facts.keys): the range loop around an index and the guards before it, a
    divisor that tests show non-zero, and a key that a test or a store shows
    present; and what the closest rule needs when none proves an operation
    (facts.closest-rule). *)

(** The rules' names, which E0204 and [show] print (facts.rules-of-acceptance).
*)
type rule =
  | Range_loop
  | Guard
  | Divisor
  | Key
  | Counting_loop
  | Shrinking_recursion

type verdict =
  | Proved of rule
  | Unproved of string
      (** With what the closest rule needs, as E0204 says it. *)

type cx = { env : Env.t; w : Accept_walk.t; signs : Accept_signs.t }
(** A walked body, with its known signs. *)

val verdict : cx -> Accept_walk.pending -> verdict option
(** The verdict of an index or a division; none for a self-call, which
    facts.shrinking-recursion reads with the others. *)
