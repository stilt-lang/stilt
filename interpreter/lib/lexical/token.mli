(** The tokens of Stilt (lexical.tokens). *)

include module type of struct
  include Token_type
end

type token = t
(** The name the parser generator expects for the token type. *)

val word : string -> t option
(** [word text] is the keyword spelled [text], if any: every word that
    lexical.reserved-words reserves has a form. *)

val contextual_keyword : string -> t option
(** [contextual_keyword text] is the contextual keyword spelled [text], if any.
*)

val punctuation : (string * t) list
(** The operator and punctuation tokens with their spellings, longest first, so
    that the first match is the maximal munch. [;] maps to [SEP]. *)

val to_string : t -> string
(** A short description for debugging output, such as [LIDENT main] or [fn]. *)
