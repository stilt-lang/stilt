(** Text beyond ASCII for generated programs: accented Latin, Greek, Cyrillic,
    CJK, digits of other scripts, combining marks, emoji and characters outside
    the Basic Multilingual Plane, as literals that write each character as
    itself or as a [\u{…}] escape (lexical.escapes). The generator knows each
    text's scalar values, so it names the byte offsets on their boundaries,
    where [slice] and [View.of] don't panic (std.str; views.making-view). *)

type scalar = { utf8 : string; source : string }
(** A scalar value, and the text a literal writes it as. *)

type t = scalar list
(** A text, as its scalar values in order. *)

val text : Pick.t -> int -> t
(** A text of [n] scalar values. *)

val fill : Pick.t -> string
(** One character that a format spec can take as its fill, as itself
    (lexical.format-specs). *)

val literal : t -> string
(** The string literal of a text, quotes included. *)

val length : t -> int
(** The length of a text in bytes. *)

val offset : t -> int -> int
(** The byte offset of the boundary before the [i]th scalar value. *)

val sub : t -> int -> int -> t
(** The scalar values from the [i]th up to the [j]th. *)

val span : Pick.t -> t -> int * int
(** Two scalar indices in order, from 0 to the text's count. *)

val bytes : Pick.t -> int list
(** Bytes for [str.from_utf8_lossy]: valid UTF-8 sequences and invalid ones,
    lone continuation bytes, truncated sequences, overlong forms, surrogates and
    values above [0x10FFFF] (std.code-points). *)
