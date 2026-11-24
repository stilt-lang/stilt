(** Float operations of numbers.ieee-754 and std.floats that OCaml doesn't
    provide exactly.

    An [f32] value is held in a [float] that binary32 represents exactly. *)

val round32 : float -> float
(** The value rounded to binary32, to nearest with ties to even. *)

val result : f32:bool -> float -> float
(** The result of an operation, rounded to binary32 for an [f32]
    (numbers.ieee-754). *)

val f32_of_decimal : string -> float
(** A decimal in the form of a float literal, rounded to binary32 in one step.
*)

val to_string : f32:bool -> float -> string
(** The shortest form that reads back as the value (numbers.printing-floats and
    numbers.float-digits). *)

val fixed : precision:int -> float -> string
(** Fixed notation with [precision] fractional digits (std.precision). *)

val scientific : f32:bool -> ?precision:int -> float -> string
(** Scientific notation, with the shortest digits or with [precision] digits
    after the point (std.scientific-notation). *)

val to_int : Ints.kind -> float -> int64 option
(** The value truncated toward zero, unless it is NaN, infinite or out of range
    (numbers.conversions). *)

val minimum : float -> float -> float
val maximum : float -> float -> float

val total_compare : float -> float -> int
(** The total order of [Ord.compare] on floats (traits.floats). *)

val parse : f32:bool -> string -> float option
(** [str.to_f64()] and [str.to_f32()] (numbers.parsing). *)
