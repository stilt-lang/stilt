(** The natives of [std.net] (std.net, std.net-listeners and std.net-streams).
    Opening, accepting and writing raise {!Eval_state.Raised} with their
    [std.io.IoError] when they fail; reads end where they fail. *)

val native : string -> Value.value array -> Value.value
(** [native name args] runs the native [name] of [std.net]. *)
