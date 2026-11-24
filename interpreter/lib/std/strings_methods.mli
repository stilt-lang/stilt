(** The native methods of [str] that std.str, std.bytes-and-scalars and
    std.code-points adds. Offsets count bytes, widths count Unicode scalar
    values, and every string is valid UTF-8. *)

val rfind : string -> string -> int option
(** The offset of the last occurrence, which for [""] is the length. *)

val drop_while_start : string -> string
(** [trim_start]: without the ASCII whitespace at its start. *)

val drop_while_end : string -> string
(** [trim_end]: without the ASCII whitespace at its end. *)

val strip_prefix : string -> string -> string option
val strip_suffix : string -> string -> string option

val split_once : string -> string -> (string * string) option
(** The text before and after the first occurrence of the separator. *)

val rsplit_once : string -> string -> (string * string) option
(** The text before and after the last occurrence of the separator. *)

val count : string -> string -> int
(** Non-overlapping occurrences, from left to right, or the number of scalar
    values plus one for [""]. *)

val replace_first : string -> string -> string -> string
val split_whitespace : string -> string list

val padding : string -> int -> string -> string
(** [padding s width fill]: the copies of [fill], the last cut short, that bring
    [s] to [width] scalar values. *)

val pad_start : string -> int -> string -> string
val pad_end : string -> int -> string -> string
val char_count : string -> int
val reverse : string -> string
val is_ascii : string -> bool

val classify : string -> (char -> bool) option
(** The test of each byte of a classification method, by its name, as
    ["is_ascii_digit"]. *)

val classified : (char -> bool) -> string -> bool
(** Whether the string isn't empty and every byte passes the test. *)

val code_points : string -> int list

val from_code_point : int -> string option
(** The string of one scalar value, or [None] for a surrogate or a value beyond
    [0x10FFFF]. *)

val from_utf8 : int list -> string option
(** The string of the bytes, or [None] unless they are valid UTF-8. *)

val from_utf8_lossy : int list -> string
(** The bytes, each maximal invalid subsequence replaced by U+FFFD. *)
