(** The lexer: source text to tokens, with separators inserted (lexical.tokens
    and lexical.separators). *)

type token = {
  token : Token.t;
  line : int;  (** 1-based line of the token's first character. *)
  col : int;  (** 1-based column, counting Unicode scalar values. *)
}

type comment = {
  text : string;  (** The text after [//] or [///]. *)
  doc : bool;  (** Whether the comment is a [///] doc comment. *)
  line : int;
  col : int;
}

type output = {
  tokens : token list;
      (** Every token, ending with [EOF]. After an error, the tokens before it,
          with no [EOF]. *)
  written : int;
      (** How many tokens the text holds as written, before separators are
          inserted or dropped (lexical.separators), [EOF] aside. *)
  comments : comment list;  (** Every comment before any error, in order. *)
  error : Diagnostic.t option;  (** The first lexical error, if any. *)
}

val tokenize : ?line:int -> ?col:int -> file:string -> string -> output
(** [tokenize ~file text] lexes the contents [text] of the source file [file].
    It stops at the first error, and keeps the tokens before it so that the
    parser can tell whether a syntax error comes first (errors.syntax-errors and
    errors.phases).

    [line] and [col], both 1 by default, give the position of the text's first
    character, for text taken from inside a file, such as a doc example. *)
