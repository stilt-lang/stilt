(** The sites of possible non-termination, the implicit effect [div] (facts.div
    and facts.descending-self-calls). *)

type context = {
  env : Env.t;
  self : Implicit_names.key option;  (** The item whose body it is. *)
  group : Implicit_names.key list;
      (** The item's recursive group, or nothing if it isn't recursive. *)
  params : (Ast.mode * Hir.var) list;
  through : Hir.var list;
      (** Its non-escaping parameters (effects.non-escaping-parameters). *)
  proofs : Accept.t option;
      (** What the rules of acceptance prove of the body (facts.counting-loops
          and facts.shrinking-recursion). *)
}

val sites : context -> Tast.block -> (Tast.expr * string * string option) list
(** The operations of a body that may not end, each with why, and what the
    closest rule of acceptance needs (facts.closest-rule): a [while] that no
    counting loop shows to end (facts.counting-loops) or a [loop]; a call
    through a function value held by a field, a local binding or an escaping
    parameter; and a call of a function of the item's own recursive group, or a
    use of one as a value, except a self-call that descends, which passes a
    strict part of one [let] parameter at every self-call, or shrinks
    (facts.shrinking-recursion). *)
