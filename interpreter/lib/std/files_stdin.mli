(** Standard input, as [std.io] reads it (std.read-line; std.io).

    Every read goes through one buffer of this module's own, never through
    [Stdlib.stdin], so that [poll_line] sees the bytes already read from the
    system as well as those the system holds: [Unix.select] sees only the
    latter. A line that one function reads is never read again by another. *)

val read_line : unit -> string option
(** The next line of stdin, waiting for it, without its [\n] or a [\r] that ends
    it, with invalid UTF-8 repaired. [None] at the end of the input, or when
    stdin can't be read. *)

val poll_line : unit -> string option
(** The next line of stdin, read as {!read_line} reads it, when a whole line, or
    the last line before the end of the input, is waiting, and [None] otherwise,
    without waiting. *)

val read_all : unit -> string
(** The rest of stdin, with invalid UTF-8 repaired, or [""] when stdin can't be
    read. *)
