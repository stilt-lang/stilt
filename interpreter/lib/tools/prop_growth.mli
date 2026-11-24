(** Whether a type holds infinitely many types (tests.generable-types and
    tests.growth-test), decided without expanding any of them. The nodes are the
    type parameters of the declarations that the types hold; an edge from [D.p]
    to [E.j] says that a field or payload of [D] holds [E] with an argument [j]
    in which [p] occurs, and it grows when [p] occurs strictly inside that
    argument. The types hold infinitely many exactly when a cycle has a growing
    edge. *)

val infinite : Env.t -> Types.ty list -> bool
(** Whether the types that these hold are infinitely many. *)
