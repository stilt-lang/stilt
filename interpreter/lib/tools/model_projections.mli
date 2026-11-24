(** Projections in the Lean model's calculus: a projection's call where a place
    is, written as the call of the projection for that access, a closure literal
    (projections.call-is-place and projections.when-projection-runs). *)

val rooted : Tast.expr -> bool
(** Whether a place is rooted in a projection's call. *)

val assign :
  Model_types.cx ->
  Ast.loc ->
  Ast.binary option ->
  Tast.expr ->
  Tast.expr ->
  Tast.expr
(** [target = v], or [target op= v], whose target is rooted in a projection's
    call. *)

val desugar : Model_types.cx -> Tast.expr -> Tast.expr
(** An expression with a projection's call where a place is, in the calculus's
    terms. *)
