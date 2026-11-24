(** Format specs in interpolations: their grammar (lexical.format-specs) and
    their meaning (std.width-fill-and-alignment, std.precision,
    std.integer-kinds, std.scientific-notation and std.format-special-values).
*)

type t = {
  fill : string;  (** One Unicode scalar value, a space by default. *)
  align : char option;  (** [<], [^] or [>]. *)
  width : int;  (** [0] when none is written. *)
  precision : int option;
  kind : char option;  (** [x], [X], [o], [b] or [e]. *)
}

val limit : int
(** The largest width or precision a spec may give. *)

val parse : string -> t option
(** The spec written between the [:] and the [}] of an interpolation, unless it
    doesn't follow the grammar. *)

(** The value an interpolation formats, when it is a number. *)
type number =
  | Int of Ints.kind * int64
  | Float of bool * float  (** Whether it is an [f32], and its value. *)
  | Not_a_number

val apply : t -> number -> string -> string
(** [apply spec number shown] formats a value whose [Show] text is [shown] by
    the spec, which the checker has found valid for the value's type. *)
