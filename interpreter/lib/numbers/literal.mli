(** Whether number literals fit their types (numbers.integer-literals,
    numbers.float-literals and numbers.negative-literals). The tests are exact:
    literals may exceed the range of OCaml's integers. *)

val int_fits : string -> negative:bool -> string -> bool
(** [int_fits text ~negative ty] tells whether the integer literal [text],
    negated when [negative], is a value of the integer type named [ty]. *)

val int_exact_in : string -> string -> bool
(** [int_exact_in text ty] tells whether the float type named [ty] represents
    the integer literal [text] exactly. *)

val float_fits : string -> string -> bool
(** [float_fits text ty] tells whether the float literal [text] rounds to a
    finite value of the float type named [ty]. *)

val int_canonical : string -> string
(** A form of the integer literal [text], which may start with [-], that two
    literals share exactly when they stand for the same value, as [0x10] and
    [16] do. *)
