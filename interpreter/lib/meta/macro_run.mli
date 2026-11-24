(** A procedural macro's run on a use (macros.running, macros.failed-uses and
    macros.step-limits): the values of its parts, the call of the macro, and how
    the run ends. *)

type call = Hir.item -> Value.value array -> Ast.loc -> Value.value

val run :
  call ->
  named:(Ast.loc -> string) ->
  source:string option ->
  Procs.use ->
  Procs.outcome
(** Runs the macro of [use] on the values of its parts, as [call] calls it, and
    gives how the run ends: its code, or the errors it raised or reached
    (macros.failed-uses and macros.step-limits). *)
