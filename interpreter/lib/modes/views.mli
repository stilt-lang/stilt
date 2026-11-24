(** Views in a body, in phase 2 of checking it (views.making-view;
    errors.phases): the views it makes of a type that can't be viewed (E0420,
    views.viewable-types), stores (E0421, views.view-types), or lets outlive
    their sources (E0422, views.escaping). The reads that views make, and E0423,
    are checked with exclusivity ({!Modes}). *)

val errors :
  Env.t ->
  file:string ->
  params:(Ast.mode * Hir.var) list ->
  Tast.block ->
  Diagnostic.t list
(** The errors of a body whose function has the parameters [params]: E0420 at
    each [View.of] or [View.all] of a type that can't be viewed; E0421 at each
    type the body writes that holds a view where none may stand, and at each
    expression that builds a value that stores a view from a view; and E0422 at
    each view that leaves the body, other than into its result from its [let]
    parameters, and at each closure that captures a view and leaves the body. *)
