(** Random choices. Every choice draws from one state, so a seed fixes the whole
    program. *)

type t = Random.State.t

val make : int -> t
(** The state of a seed. *)

val below : t -> int -> int
(** An integer from 0 to [n - 1]. *)

val between : t -> int -> int -> int
(** An integer from [lo] to [hi], both included. *)

val chance : t -> float -> bool
(** [true] with probability [p]. *)

val one : t -> 'a list -> 'a
(** One of the values, each as likely as the others. *)

val weighted : t -> (int * 'a) list -> 'a
(** One of the choices, each as likely as its weight. Choices of weight 0 are
    never taken, and at least one weight must be positive. *)

val times : int -> (unit -> 'a) -> 'a list
(** [n] values made by [f], in order. *)

val bits64 : t -> int64
(** 64 random bits. *)

val run : t -> (int * (unit -> 'a)) list -> 'a
(** Runs one of the thunks, each as likely as its weight. *)
