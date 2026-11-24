(** How deep a file's brackets and interpolations nest (lexical.nesting). *)

val levels : int
(** How many levels a file may nest. *)

val in_tokens : file:string -> Lexer.token list -> Diagnostic.t option
(** [in_tokens ~file tokens] is the breach of lexical.nesting, E0008, among the
    tokens that {!Lexer.tokenize} gives of the file [file], if they nest deeper
    than {!levels}. *)

val too_deep : file:string -> string -> Diagnostic.t option
(** [too_deep ~file text] is the breach of lexical.nesting in the normalized
    text of the source file [file], E0008, if it nests deeper than {!levels}. *)
