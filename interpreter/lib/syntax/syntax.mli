(** Parsing a source file into its syntax tree (syntax.tree-form and
    errors.parts). *)

val parse :
  ?native:bool ->
  file:string ->
  string ->
  (Ast.module_ * Diagnostic.t list, Diagnostic.t) result
(** [parse ~file text] lexes and parses the contents [text] of the source file
    [file], and attaches each run of doc comments to its declaration
    (program.doc-comments). The result holds the warnings for its [//] comments
    that hold code (lexical.commented-out-code). A file may declare native
    types, [type T = ?], only if [native], which only the standard library's
    files are (views.std-view); elsewhere the [?] is a syntax error.

    On failure, the result is the file's first syntax error, as
    [syntax.first-error] defines it. *)

val placed_with_examples :
  ?line:int -> file:string -> string -> Lexer.output * Diagnostic.t list
(** [placed_with_examples ?line ~file text] is the output of the lexer for
    [text], whose first line is the file's line [line], 1 by default, with each
    doc comment in place as {!placed} gives it, and the syntax errors of its doc
    examples and properties. *)

val comment_warnings : file:string -> Lexer.comment list -> Diagnostic.t list
(** The warnings for the [//] comments among these that hold code
    (lexical.commented-out-code). *)

val placed : file:string -> string -> Lexer.output
(** The output of the lexer for the contents of [file], with each doc comment in
    place as a token: a [DOC] before the declaration it documents, or a
    [MISPLACED_DOC]. A doc example that doesn't parse is left out of its [DOC]
    token. *)

val parse_part :
  file:string -> Lexer.token list -> (Ast.module_, Diagnostic.t option) result
(** Parses tokens as a file of the program, giving its first syntax error, or
    [Error None] if the tokens run out before the parser is done, as they do
    before a lexical error. A native type is a syntax error, as {!parse} gives
    it outside the standard library, which never has syntax errors. *)
