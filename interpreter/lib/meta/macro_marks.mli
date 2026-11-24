(** The marks that keep a macro's expansion hygienic (macros.hygiene).

    An identifier that a template writes is marked, in its expansion, with the
    number of that expansion, as [tmp#1], which no program can write. A name
    that the template binds is then fresh: no name the user wrote is spelled as
    it is. Every other marked name resolves where the macro is declared. A
    fragment's tokens stay unmarked, and resolve where the use is. *)

val mark : int -> string -> string
(** [mark n name] is [name] as the expansion [n] writes it. *)

val split : string -> (string * int) option
(** The name and the expansion of a marked name, or [None] for a name as the
    user wrote it. *)

val base : string -> string
(** The name as written, without its mark. *)

val hole : string -> string
(** [hole name] stands for the fragment [name] when a template is checked where
    it is declared (macros.checked-templates): a name that means nothing and
    reports nothing. *)

val is_hole : string -> bool
