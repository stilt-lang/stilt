(** A macro's templates as tokens: expanded for a use, or with holes where they
    are declared (macros.checked-templates, macros.expansion and
    macros.hygiene). *)

type form = Expr | Pattern | Type

val substitute :
  id:int ->
  at:Ast.loc ->
  Ast.tree list ->
  Macro_match.bindings ->
  Lexer.token list
(** [substitute ~id ~at template bindings] is the expansion numbered [id] of
    [template]: each fragment replaced by the tokens it matched, an expression
    or a pattern between parentheses, so that it stays one form, and each
    repetition repeated once for each round of its fragments, with its separator
    between. The template's own tokens are at [at], the position of the use, and
    each identifier among them that isn't a member, after a [.], is marked with
    [id] (macros.hygiene). *)

val holes : form -> (string * string) list -> Ast.tree list -> Lexer.token list
(** [holes form kinds template] is [template] where its macro is declared, with
    each repetition repeated once, and each fragment, of the kind that [kinds]
    gives it, standing as a form of its kind: a name that reports nothing for an
    expression, a name, an [Upper] name or a type, [_] for a pattern and [{}]
    for a block. A fragment that can't stand in [form], an expression in a
    pattern or a pattern in an expression, is a [$], which no form holds
    (macros.expansion). *)

val parse_expr :
  file:string ->
  at:Ast.loc ->
  Lexer.token list ->
  (Ast.expr, Diagnostic.t option) result
(** Parses tokens as one expression, with an end after them at [at]. *)

val parse_pattern :
  file:string ->
  at:Ast.loc ->
  Lexer.token list ->
  (Ast.pattern, Diagnostic.t option) result
(** Parses tokens as one pattern, with an end after them at [at]. *)

val parse_type :
  file:string ->
  at:Ast.loc ->
  Lexer.token list ->
  (Ast.ty, Diagnostic.t option) result
(** Parses tokens as one type, with an end after them at [at]
    (macros.part-forms). *)
