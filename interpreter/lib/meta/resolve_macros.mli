(** The uses of macros, expanded as names are resolved (macros.uses,
    macros.expansion, macros.nested-expansions and macros.errors-in-expansions).
*)

open Resolve_context

val find : ctx -> Ast.path -> (Hir.item * macro) option
(** The macro a use's path names, resolved as a function's name is, so that no
    local hides it (macros.uses). Anything else the path names is an error, and
    so is a macro whose declaration has one, but which reports nothing more. *)

val expand :
  ctx ->
  Ast.loc ->
  Ast.path ->
  Ast.tree list ->
  Macro_expand.form ->
  (ctx -> Lexer.token list -> ('t, Diagnostic.t option) result) ->
  (ctx -> 't -> 'r) ->
  'r option
(** [expand ctx loc path groups form parse resolve] expands the use at [loc] of
    the macro [path], whose groups are [groups], where a [form] stands: the
    macro must make that form (E0223, at the path), an arm must match the use
    (E0222, at the furthest token an arm reached) or a procedural macro's run
    must give an expansion (macros.running), the use must lie inside fewer than
    128 expansions of either kind (E0224, at the use the user wrote), and the
    expansions of the use the user wrote must hold at most 100,000 tokens in all
    (E0231, there; macros.expansion-size), either error ending that use. The
    expansion's tokens are parsed with [parse] and resolved with [resolve], in a
    context that marks them as an expansion's. [None] after an error, and for
    every use in a template that is checked where its macro is declared, which
    expands nothing (macros.checked-templates). *)

val splice : ctx -> Hir.place -> Ast.expr -> 'a -> 'a
(** [splice ctx place s none] records the splice [s], a [Q_splice] or a
    [Q_spread] of a quote being resolved, where [place] says it stands, and
    gives [none], which stands for it in the quote's tree (macros.splices). *)
