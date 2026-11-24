(** The native operations on [str] (std.str and std.show-names-and-escapes).
    Offsets count bytes, and every string is valid UTF-8. *)

val find : string -> string -> int option
(** [find s sub] is the offset of the first occurrence of [sub] in [s]. *)

val occurs_at : string -> string -> int -> bool
(** [occurs_at s sub i] tells whether [sub] occurs in [s] at offset [i]. *)

val is_space : char -> bool
(** Whether a byte is ASCII whitespace, as [trim] strips it (std.str). *)

val is_boundary : string -> int -> bool
(** Whether an offset, from [0] to the length, starts no byte inside a UTF-8
    sequence. *)

val chars : string -> string list
(** One string per Unicode scalar value. *)

val split : string -> string -> string list
val lines : string -> string list
val trim : string -> string
val replace : string -> string -> string -> string

val repair : string -> string
(** The bytes, with each maximal invalid UTF-8 subsequence replaced by U+FFFD
    (std.read-line). *)

val quote : string -> string
(** The string as [show_nested] shows it: quoted and escaped. *)
