(** The lexical layer of TOML 1.0 (packages.manifest): a cursor over a text, and
    the reading of its scalar values. Every error is at the first character from
    which no TOML document can continue. *)

exception Syntax of int * string
(** Why a text isn't TOML 1.0, at a byte offset. *)

type cursor = { text : string; mutable pos : int }

(** The kinds of number that {!number} reads. *)
type number = Int_number | Float_number | Date_number

val peek : cursor -> char option
val peek_at : cursor -> int -> char option
val bump : cursor -> unit
val eat : cursor -> char -> bool

val fail : cursor -> string -> 'a
(** Raises {!Syntax} at the cursor. *)

val expect : cursor -> char -> string -> unit

val ws : cursor -> unit
(** Spaces and tabs. *)

val is_control : char -> bool
(** Whether a byte is a control character that TOML allows only as a tab or in a
    newline. *)

val newline : cursor -> bool
(** Reads [\n] or [\r\n], if one is here. *)

val comment : cursor -> unit
(** A comment, from its [#] to the end of its line, if one is here. *)

val word : cursor -> string -> unit
(** Reads a word exactly, as [true] or [inf]. *)

val digit_of : int -> char -> int option
(** The value of a digit in a radix. *)

val number : cursor -> number
(** A number, a date or a time. *)
