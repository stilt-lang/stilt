(** Staging annotations (meta.staging-annotations): what a [comptime] marks as
    known at compile time. *)

val errors :
  file:string ->
  params:(Ast.mode * Hir.var) list ->
  Tast.block ->
  Diagnostic.t list
(** E0349 for each part of a body's staging annotations that isn't a static
    expression (meta.static-expressions and meta.not-static): the iterable of a
    [comptime for], the condition of every [if] and the scrutinee of every
    [if let] of a [comptime if]'s chain, and the scrutinee and guards of a
    [comptime match], each reported once, at its first part that isn't static in
    evaluation order. [params] are the body's parameters, which are known only
    at run time. *)
