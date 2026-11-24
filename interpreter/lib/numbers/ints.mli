(** Integer arithmetic at the eight widths of numbers.numeric-types.

    A value of a kind is held in an [int64]: signed values, and unsigned ones
    below 2^63, as themselves, and [u64] values from 2^63 on by their bit
    pattern. Operations that numbers.integer-panics says panic raise
    {!Fault.Panic}. *)

type kind = { bits : int; signed : bool }

val of_name : string -> kind option
(** The kind of an integer type's name, such as ["u8"]. *)

val name : kind -> string
val min_value : kind -> int64
val max_value : kind -> int64

val wrap : kind -> int64 -> int64
(** The low bits of a value, for the kind (numbers.wrapping-conversions). *)

val compare : kind -> int64 -> int64 -> int
val to_string : kind -> int64 -> string

(** {1 Arithmetic (numbers.integer-panics, numbers.division-and-remainder,
    numbers.wrapping, numbers.shifts and numbers.bitwise-operators)} *)

val add : kind -> int64 -> int64 -> int64
val sub : kind -> int64 -> int64 -> int64
val mul : kind -> int64 -> int64 -> int64
val div : kind -> int64 -> int64 -> int64
val rem : kind -> int64 -> int64 -> int64
val neg : kind -> int64 -> int64
val add_wrap : kind -> int64 -> int64 -> int64
val sub_wrap : kind -> int64 -> int64 -> int64
val mul_wrap : kind -> int64 -> int64 -> int64
val logand : int64 -> int64 -> int64
val logor : int64 -> int64 -> int64
val logxor : int64 -> int64 -> int64
val lognot : kind -> int64 -> int64
val shift_left : kind -> by:kind -> int64 -> int64 -> int64

val shift_right : kind -> by:kind -> int64 -> int64 -> int64
(** [shift_left k ~by a n] shifts [a] of kind [k] by [n], whose kind is [by]: an
    amount has an integer type of its own, and panics when it is negative in
    that type or at least the width of [k] (numbers.shift-amounts). *)

(** {1 Conversions (numbers.conversions, numbers.wrapping-conversions and
    numbers.parsing)} *)

val fits : from:kind -> kind -> int64 -> bool
(** [fits ~from into a] tells whether the value [a] of kind [from] is a value of
    kind [into]. *)

val lossless : from:kind -> kind -> bool
(** Whether every value of [from] is a value of the other kind, so that the
    conversion returns no [Option]. *)

val to_float : kind -> int64 -> float
(** The value rounded to an [f64], to nearest with ties to even. *)

val to_f32 : kind -> int64 -> float
(** The value rounded to an [f32] in one step, to nearest with ties to even. *)

val of_literal : string -> int64
(** The value of an integer literal as written, without [_] and perhaps with a
    radix prefix. The literal fits its type, which the checker ensures. *)

val parse : kind -> string -> int64 option
(** [str.to_T()] for an integer type. *)

val to_base : kind -> base:int -> upper:bool -> int64 -> string
(** The value in base 2, 8 or 16, a negative one as its two's complement at the
    kind's width (std.integer-kinds). *)
