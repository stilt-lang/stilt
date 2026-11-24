(** The methods of the integer types that std.integers adds, at the widths of
    {!Ints}. Those that panic raise {!Fault.Panic}, as {!Ints} does. *)

val checked_add : Ints.kind -> int64 -> int64 -> int64 option
val checked_sub : Ints.kind -> int64 -> int64 -> int64 option
val checked_mul : Ints.kind -> int64 -> int64 -> int64 option

val saturating_add : Ints.kind -> int64 -> int64 -> int64
(** The exact sum, clamped to the kind's range. *)

val saturating_sub : Ints.kind -> int64 -> int64 -> int64

val pow : Ints.kind -> int64 -> int64 -> int64
(** [pow k a exp], with [exp] a [u32]: [overflow] when the exact power doesn't
    fit. *)

val div_euclid : Ints.kind -> int64 -> int64 -> int64
(** The quotient whose remainder is never negative: [divide-by-zero] for a zero
    divisor, and [overflow] for [MIN] by [-1]. *)

val rem_euclid : Ints.kind -> int64 -> int64 -> int64
(** The remainder of {!div_euclid}, which panics as it does. *)

val count_ones : Ints.kind -> int64 -> int64
(** The number of 1 bits at the kind's width, in two's complement. *)

val leading_zeros : Ints.kind -> int64 -> int64
(** The number of 0 bits above the highest 1 bit, which for 0 is the width. *)

val trailing_zeros : Ints.kind -> int64 -> int64
(** The number of 0 bits below the lowest 1 bit, which for 0 is the width. *)

val gcd : Ints.kind -> int64 -> int64 -> int64
(** The greatest common divisor of the magnitudes: [overflow] when it doesn't
    fit, as for [MIN] and 0. *)

val lcm : Ints.kind -> int64 -> int64 -> int64
(** The least common multiple of the magnitudes, and 0 when either is 0:
    [overflow] when it doesn't fit. *)
