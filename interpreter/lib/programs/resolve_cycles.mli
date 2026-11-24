(** Step 4 of name resolution: modules can't depend on one another in a cycle
    (program.no-cycles). *)

val check_cycles : Resolve_context.state -> Resolve_context.Sset.t -> unit
(** [check_cycles st modules] reports the cycles among the references between
    [modules] that [st] records. Each strongly connected component of their
    graph that holds a cycle is one error, at the last reference inside it
    (errors.primary-spans). *)
