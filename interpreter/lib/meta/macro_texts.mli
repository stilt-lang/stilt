(** The texts that macros read (macros.named-files): the places of a text's
    bytes, in a string literal of the use's file or in a file a use names. *)

type piece = { at : int; bytes : int; first : int; stop : int }
(** A piece of a literal's value, an escape or one character, with the columns
    of its source, from [first] to before [stop]. *)

val raw_literal : string -> Ast.loc -> string option
(** The source of a string literal at [loc], from its opening quote, in the text
    of its file. *)

val offset : string -> Ast.loc -> int
(** The byte of [text] at a line and a column. *)

val span : Macro_values.text -> start:int -> stop:int -> Macro_values.span
(** The span of the bytes from [start] to [stop] of a text: the characters of
    its literal that write them, or their places in the file that a literal
    names. *)

val place : Macro_values.text -> Ast.loc -> Macro_values.span
(** Where a position of the text's own lines is written. *)
