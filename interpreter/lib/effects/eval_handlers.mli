(** Handlers at run time (handlers.with and handlers.resuming): deep, and
    one-shot, on the effects of OCaml 5. *)

val literal :
  Eval_state.t ->
  Eval_state.frame ->
  expr:(Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value) ->
  Tast.handler ->
  Value.value
(** A handler literal's value, its operations' closures made in the frame. *)

val install :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Value.value ->
  (unit -> Value.value) ->
  Value.value
(** [install t fr at h run] runs [run] with the handler [h] installed by the
    [with] at [at] in [fr], innermost (handlers.with). A handler of [async]
    installs nothing: every task runs to its end where it starts
    (tasks.sequential-run and tasks.same-output-under-every-handler). A handler
    that takes control captures the rest of the block at each performance, which
    a body that never resumes drops. *)

val perform :
  call:(Value.fn -> Value.value) ->
  values:(unit -> Value.value array) ->
  Hir.item ->
  string ->
  Value.value
(** [perform ~call ~values eff op] performs [op] on the nearest handler of [eff]
    (handlers.with). One that resumes at once is called by [call] here, without
    itself in the stack, so that its body performs its own effect outside it;
    one that takes control is given [values ()], the arguments' values. *)

val resume : Value.value -> Value.value
(** [resume(v)] in the body of the operation that runs, which runs the rest of
    its [with]'s block from the performance and gives what the block ends with
    (handlers.resuming). *)
