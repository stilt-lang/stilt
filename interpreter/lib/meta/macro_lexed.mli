(** Tokens as a macro reads them (macros.tokens-and-code): the tokens of
    lexical.tokens, as written, each group one token holding its own, each
    interpolated string one token, without the separators that newlines insert,
    and without doc comments. *)

type source = {
  span : Lexer.token -> Macro_values.span;
  text : Lexer.token -> Macro_values.text;
  written : string option;
}
(** Where the tokens are written: a token's span, a string literal's text, and
    the text where they are written, when it is known, from which a number's
    text comes as written. *)

val tokens : source -> Lexer.token list -> Macro_values.token list
(** The tokens of [lexed] as a macro reads them: each group and each
    interpolated string one token, without the separators that newlines insert.
*)

val code : Macro_values.token list -> Lexer.token list
(** The tokens as code, with no terminator at their top level, as inside [( … )]
    (macros.part-forms; lexical.inside-brackets): a group keeps its own, which
    lexical.terminator-insertion inserts inside a [{ … }]. *)
