(** What a checked program tells of its procedural macros
    (macros.procedural-declarations and macros.step-limits). *)

val state : Hir.program -> string -> string -> Procs.state
(** macros.procedural-declarations: the inputs and result of the macro [name] of
    [home]. *)

val named : Hir.program -> string -> Ast.loc -> string
(** macros.step-limits: the name of the function of [home] whose name is at
    [at]. *)
