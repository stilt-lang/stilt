(** Modes and exclusivity (modes.law). *)

val errors :
  file:string ->
  params:(Ast.mode * Hir.var) list ->
  Tast.block ->
  Diagnostic.t list
(** A body's modifications of what it can't modify, overlapping [inout]
    arguments, modifications of a place that a [for] loop reads, and
    modifications of a place that a view reads (views.change-while-viewed).
    [params] are the parameters of the body's function. *)
