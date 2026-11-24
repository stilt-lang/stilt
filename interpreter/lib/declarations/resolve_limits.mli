(** The [without] clauses of module headers and functions, which limit the facts
    that the compiler infers about them (program.header-limits;
    declarations.limits). Each error is reported and the limit it concerns is
    then ignored. *)

val of_header :
  Resolve_context.state ->
  file:string ->
  Ast.without list ->
  Hir.limit Hir.node list
(** The limits that a header's clauses set. A second clause is an error at its
    [without], and so is a limit named again in the first, at its second
    occurrence. *)

val of_fn : Resolve_context.ctx -> Ast.without option -> Hir.limit Hir.node list
(** The limits that a function's clause sets. A limit named again is an error at
    its second occurrence. *)
