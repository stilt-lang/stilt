(** The natives of [std.c], the prelude's [with_ptr], [with_mut_ptr] and
    [with_c_str], and the calls of foreign functions (c.module-std-c,
    c.lending-methods and c.calls and c.both-implementations). *)

val lends : string list
(** The names of the prelude's methods that lend C a list or a string. *)

val lend :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  string ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [lend t fr loc name targs args] runs the lending method [name] on its
    receiver and closure, the list's element type first in [targs]. A list lent
    by [with_mut_ptr] is left in [args] holding what C wrote.

    @raise Fault.Panic with [nul-in-string] for a string that holds a NUL.
    @raise Eval_state.Stopped in a macro's run, which can't reach C. *)

val native :
  Eval_state.t ->
  Tast.callee ->
  Types.ty list ->
  Value.value array ->
  Value.value
(** [native t callee targs args] runs a native of [std.c], or calls a foreign
    function.

    @raise Eval_state.Fatal for a foreign function that no library defines.
    @raise Eval_state.Stopped in a macro's run, which can't reach C. *)
