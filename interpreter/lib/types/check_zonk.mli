(** Elaborated code, with every type variable replaced by its solution
    (types.inferred-per-body and types.undecided-types), or every type and row
    replaced as a function says. *)

val map_expr :
  ty:(Types.ty -> Types.ty) ->
  row:(Types.row -> Types.row) ->
  Tast.expr ->
  Tast.expr
(** The expression with [ty] applied to the type of each of its nodes and to
    each type it names, and [row] to the row each call performs. *)

val map_block :
  ?spec:(Tast.expr -> string -> string) ->
  ?node:(Tast.expr -> Tast.expr) ->
  ty:(Types.ty -> Types.ty) ->
  row:(Types.row -> Types.row) ->
  Tast.block ->
  Tast.block
(** [map_expr] over a block, with [spec] applied to each splice's format spec,
    with the splice as it was written, and [node] to each node as it was
    written, before its parts are mapped. *)

val zonk_expr : Tast.expr -> Tast.expr
val zonk_block : Tast.block -> Tast.block
