(** Checks a test's program and prints its diagnostics as
    conformance.diagnostic-lines compares them: a file, a line and a code each,
    or [ok] when there are none. *)

open Stilt

val sources : (string * string) list -> Program.source list
(** The program made of [files], each a path and a text. *)

val check : (string * string) list -> unit
(** Checks the directory program made of [files], each a path and a text. *)

val main : string -> unit
(** Checks the single-file program [text], as the file [main.lt]. *)

(** The same checks, printing only the errors, which leaves out warnings. *)
module Errors : sig
  val check : (string * string) list -> unit
  val main : string -> unit
end
