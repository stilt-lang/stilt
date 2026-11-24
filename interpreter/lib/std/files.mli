(** The files of [std.fs] (std.fs), whose errors are those of every I/O
    operation. {!Files_stdin} reads standard input. *)

(** Why an operation failed: the variants of [std.io.IoError], in order. *)
type error = Missing | Denied | Invalid_utf8 | Other

val error_of : Unix.error -> error
(** The failure that a system error is. *)

val read : string -> (string, error) result
(** The contents of a file, which must be UTF-8. *)

val read_bytes : string -> (string, error) result
(** The bytes of a file, whatever they are. *)

val write : string -> string -> (unit, error) result
(** [write path text] creates or replaces a file. *)

val append : string -> string -> (unit, error) result
(** [append path text] adds [text] at the end of a file, creating it. *)
