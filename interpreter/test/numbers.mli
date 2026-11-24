(** What the tests of numeric operations share. *)

open Stilt

val kind : string -> Ints.kind
(** The integer kind named [name], such as [i8]. *)

val option : ('a -> unit) -> 'a option -> unit
(** [option show o] prints [x] with [show] when [o] is [Some x], and [None]
    otherwise. *)
