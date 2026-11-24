(** The tokens of macros: the atoms of the syntax tree as tokens of the parser,
    and token trees as the tokens they hold (macros.tokens-and-code). *)

val stands_for_itself : Token.t -> bool
(** Whether a token can be a [MACRO_TOKEN]: any token but a bracket, [$] and a
    separator, as [reference/03-syntax.md] defines [TOKEN]. *)

val atom : Token.t -> Ast.atom
(** The atom of a token that stands for itself, or of a separator. *)

val token : Ast.atom -> Token.t
(** The token an atom stands for. *)

val opener : Ast.delim -> Token.t
val closer : Ast.delim -> Token.t

val at : Ast.loc -> Token.t -> Lexer.token
(** A token at a position. *)

val loc : Lexer.token -> Ast.loc
(** Where a token is. *)

val flatten : Ast.tree list -> Lexer.token list
(** The tokens of token trees, each group between its brackets, at the positions
    where they are written. Trees hold no fragment or repetition. *)

val describe : Token.t -> string
(** A token as an error names it, such as [`,`] or [the end of the group]. *)
