(** The words that other languages begin a declaration with, which begin a part
    of their own (syntax.parts), and what a part that begins with one declares
    when it breaks (errors.broken-parts and errors.broken-blocks). *)

val starts : block:bool -> Token.t -> Token.t option -> bool
(** Whether a token is such a word, given the token after it: before a name, or
    before [fn] for [async] and [mutating]. In a block, only those that begin a
    function. *)

val kind :
  Lexer.token array -> int -> int -> (int * [ `Fn | `Type | `Trait ]) option
(** What a part from the token at the index to the bound declares, if it begins
    with such a word, with the index of the token before its name. *)
