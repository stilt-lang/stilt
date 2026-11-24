(** Yielding exactly once (projections.once-on-every-path): every path through a
    projection's body runs one [yield], outside every loop and every [try] with
    arms, and a path that raises or panics at most one. *)

val errors : file:string -> at:Ast.loc -> Tast.block -> Diagnostic.t list
(** The E0424 errors of a projection's body, whose closing brace is at [at]. *)
