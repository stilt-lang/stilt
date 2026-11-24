(** The native functions of [std.io], [std.fs], [std.cli], [std.clock],
    [std.math] and [std.random] that std.math, std.io and std.fs add, which call
    no code of the program. What [io.write] writes reaches stdout with each
    newline (program.output-flushing). A failed operation of [std.fs] raises
    {!Eval_state.Raised} with its [std.io.IoError]. *)

val native :
  Eval_state.t -> string -> string -> Value.value array -> Value.value
(** [native t home name args] runs the function [name] of the module [home]. *)

val io_error : string -> Files.error -> 'a
(** Raises the [std.io.IoError] of a failure at a path. *)

val bytes_value : string -> Value.value
(** The [List<u8>] of a string's bytes, reserved as the heap holds it. *)

val bytes_of : Value.value -> string
(** The bytes of a [List<u8>]. *)
