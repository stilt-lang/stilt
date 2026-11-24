(** The natives of [std.process] (std.process-starting, std.process-runs and
    std.children). A command that can't start, and a write to a child that
    fails, raise {!Eval_state.Raised} with its [std.io.IoError]. *)

val native : Eval_state.t -> string -> Value.value array -> Value.value
(** [native t name args] runs the native [name] of [std.process]. *)
