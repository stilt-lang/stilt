(** Literals, as lexical.integer-literals, lexical.float-literals and
    lexical.string-literals writes them. Values near the ends of each range are
    more likely than the rest, since that is where implementations disagree. *)

val bounds : Ty.int_kind -> string * string
(** The least and the greatest value of an integer type, as decimal text. *)

val int : Pick.t -> Ty.int_kind -> string
(** An integer literal that a value of the kind can hold, as decimal text. *)

val float : Pick.t -> string
(** A finite float that every float type can hold. *)

val string_body : Pick.t -> string
(** The text inside a string literal, ASCII only, with the escapes of
    lexical.escapes. *)

val string : Pick.t -> string
(** A string literal. *)
