(** The separators that the lexer inserts at the newlines that end statements,
    and drops where they separate nothing (lexical.terminator-insertion,
    lexical.inside-brackets and lexical.separators). *)

type token = {
  token : Token.t;
  line : int;  (** 1-based line of the token's first character. *)
  col : int;  (** 1-based column, counting Unicode scalar values. *)
}
(** A token where the lexer found it, as {!Lexer.token} exports it. *)

val insert_separators : token list -> token list
(** Inserts a separator at each newline that ends a statement
    (lexical.terminator-insertion and lexical.inside-brackets): none before a
    line that begins with [without] and a limit. The tokens end with [EOF]. *)

val drop_empty_separators : token list -> token list
(** Drops the separators that separate nothing (lexical.separators). *)
