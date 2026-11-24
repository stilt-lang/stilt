(** Phases 2 and 3 of checking each body (errors.phases), after type checking.

    Phase 2 runs on each body that type checking found no error in: marking
    (effects.marking), exhaustiveness (patterns.non-exhaustive-matches),
    exclusivity (modes.law), views (views.reads-that-last and
    views.change-while-viewed), staging annotations (meta.staging-annotations)
    and, in a body that a [without] clause limits, implicit effects
    (facts.implicit-effects). Phase 3 gives warnings, for each body that phase 2
    found no error in, and compares the bodies of functions with one another
    (docs.duplicate-bodies). *)

val check :
  std:bool ->
  text:(string -> string) ->
  Env.t ->
  Hir.program ->
  Tast.program ->
  Diagnostic.t list
(** The diagnostics of phases 2 and 3 for every body of the program, the
    duplicate bodies of docs.duplicate-bodies among its warnings, whose tokens
    are counted in the text of each file that [text] gives. The standard
    library's bodies are checked only if [std], and get no warnings: an
    executable built with the library's trees checked them when it was built
    (Driver.std_snapshot).

    @raise Failure
      if [std] and the standard library has errors, which is a bug in it. *)
