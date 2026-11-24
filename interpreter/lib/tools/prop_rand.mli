(** The numbers that a property's cases are drawn from (tests.seeds and
    tests.draws): its seed, the 64-bit FNV-1a hash of its text, and for each
    case a SplitMix64 generator started at the seed plus the case's number.
    Every operation is modulo 2⁶⁴, on [int64]s read as unsigned. *)

val seed : string -> int64
(** The FNV-1a hash of a property's text, in UTF-8. *)

type t
(** A generator, whose state each draw advances. *)

val create : int64 -> int -> t
(** [create seed i] is the generator of case [i]. *)

val next : t -> int64
(** The next number: SplitMix64's mix of the state after adding
    [0x9e3779b97f4a7c15] to it. *)

val below : t -> int64 -> int64
(** [below g n] is [next g] modulo [n], read as unsigned, for [n] at least 1. It
    draws one number even when [n] is 1. *)

val below_int : t -> int -> int
(** {!below} for a bound that an [int] holds. *)
