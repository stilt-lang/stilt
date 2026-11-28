(** A program as the Lean model's calculus writes it, for its executable
    semantics (formal/Stilt/Run): [main] and the functions it reaches, with the
    record and variant types they name. *)

val export :
  ?erroneous:bool ->
  ?hir:Hir.program ->
  Env.t ->
  Tast.program ->
  (string, string) result
(** The program as JSON, or the first form it uses that the calculus lacks. A
    program with errors, [erroneous], is written with its code that has errors
    as a panic of the kind [check-error], and marked so that its run ends with
    status 2 (program.programs-with-errors). A program without [main] is one
    that runs nothing and ends with status 2 (program.missing-main). With [hir],
    the program's declarations as kinds read them are written too, for the
    model's checks of kinds. *)
