(** The demands on the thread axes of modes (modes.fixed-values,
    modes.contended-values and modes.demands): a value put in a [Shared<T>] and
    a task's function must be [portable] (shared.tasks-and-modes), and a closure
    that [std.par] runs must be [calm] and [portable]
    (par.what-runs-in-parallel). *)

val demanded : Tast.callee -> int -> bool
(** Whether a demand reads the argument of a call at this position, the
    receiver's first, which its diagnostic reports in place of the view's. *)

val errors : Env.t -> file:string -> Tast.block -> Diagnostic.t list
(** The demands that a body's calls fail: E0432 for a value given to
    [Shared.new] that holds a view, at the value, or a task's function that
    captures one, at the capture; E0431 for a closure given to [std.par] that
    reaches a [Shared<T>] or a view, at the argument. *)
