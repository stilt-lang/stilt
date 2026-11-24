(** Quotes and their splices (macros.quote and macros.splices). *)

val quote : Check_state.ctx -> Ast.loc -> Hir.quote -> Tast.expr
(** A quote, of the type of the code it writes, [meta.Expr], [meta.Type],
    [meta.Pattern] or [meta.FieldInit], with each splice checked with no
    expected type. Whether its type fits where it stands is decided at the end
    of the body, by {!fit}. *)

val fit : Check_state.state -> unit
(** E0311 at each splice whose type doesn't fit where it stands: a [meta.Expr]
    as an expression, a [meta.Pattern] as a pattern, a [meta.Type] as a type, a
    [meta.Name] as a binding, a variable or a field, a [str], an integer, a
    [bool] or, as an expression only, a float as a literal, and a [List] of one
    of these spread among elements, or of [meta.FieldInit] among a record's
    fields. *)
