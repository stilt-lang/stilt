(** Effects: the rows that code performs, fitted into the rows that must hold
    them (effects.inference and effects.missing-effects). *)

val perform : Check_state.ctx -> Types.row -> Ast.loc -> unit
(** Records that the code at [loc] performs the effects of a row. *)

val reporter :
  ?unhandled:bool ->
  Check_state.state ->
  Ast.loc ->
  Check_unify.problem list ->
  unit
(** A reporter of what a row can't hold, which reports each kind of problem
    once. Each row that effects are fitted into has its own reporter. With
    [unhandled], for the body of [main], a test or a doc example, a user-defined
    effect that the row lacks is E0512 rather than E0502
    (handlers.no-effect-reaches-main). *)

val settle :
  ?unhandled:bool ->
  ?handled:Types.handled ->
  Check_state.state ->
  (Types.row * Ast.loc) list ->
  Types.row ->
  unit
(** Fits the effects performed so far, given latest first, into a row, in the
    order they were performed. Each missing effect is reported where it first
    occurs. [handled] is what a handler around the whole body handles. *)
