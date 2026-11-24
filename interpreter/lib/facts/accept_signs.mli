(** Known signs (facts.known-signs): the integer expressions known non-negative,
    and those known positive, each in the body it is evaluated in. *)

type t

val of_walk : Accept_walk.t -> t
(** The bindings of a walked body known non-negative, by the greatest fixed
    point of the rule, so that [a = a + 1] keeps [a] known non-negative. *)

val nonneg : t -> Tast.expr -> int -> bool
(** Whether an expression of the body numbered [body] is known non-negative. *)

val positive : t -> Tast.expr -> int -> bool
(** Whether an expression of the body numbered [body] is known positive. *)
