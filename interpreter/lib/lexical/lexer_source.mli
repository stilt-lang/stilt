(** The source text, as the lexer reads it: a cursor over its bytes, the errors
    at its positions, the classes of its characters, and the check of its
    encoding (lexical.source-text). *)

exception Error of { code : Code.t; line : int; col : int; message : string }
(** A lexical error, with its code and its position. *)

type cursor = {
  src : string;
  mutable pos : int;
  mutable line : int;
  mutable line_start : int;  (** Byte offset of the current line's start. *)
  first_line : int;
  first_col : int;  (** The column of the text's first character. *)
  mutable counted : int * int;
      (** The column of a byte of the current line that [column] counted to. *)
}
(** A position in the source text: a byte offset, and the line it falls on. *)

val cursor : line:int -> col:int -> string -> cursor
(** A cursor at the start of a text whose first character sits at [line] and
    [col]. *)

val at_end : cursor -> bool

val peek : cursor -> int -> char
(** [peek c k] is the byte [k] places ahead, or NUL past the end. Callers that
    must tell a NUL in the text from the end check {!at_end}. *)

val advance : cursor -> int -> unit
(** [advance c n] moves [n] bytes ahead, on the same line. *)

val newline : cursor -> unit
(** Moves past a newline. *)

val column : cursor -> int -> int
(** [column c offset] is the column of byte [offset] on the current line, in
    Unicode scalar values. *)

val fail : ?offset:int -> cursor -> Code.t -> string -> 'a
(** [fail c code message] raises {!Error} at byte [offset] of the current line,
    the cursor's by default. *)

val is_letter : char -> bool
(** An ASCII letter. *)

val is_ident_char : char -> bool
(** A character that can continue an identifier (lexical.identifiers). *)

val is_digit : int -> char -> bool
(** [is_digit base ch] tells whether [ch] is a digit in [base], which is 2, 8,
    10 or 16. *)

val normalize : line:int -> col:int -> string -> string
(** Checks lexical.source-text: the text must be UTF-8 with no byte-order mark,
    and a carriage return may only precede a newline. Returns the text with each
    ["\r\n"] replaced by ["\n"].

    @raise Error if it doesn't hold. *)
