(** The declarations of macros, checked before any use of one is expanded
    (macros.syntax-declarations, macros.patterns and macros.templates). *)

val declare_all :
  Resolve_context.env ->
  Resolve_context.scope list ->
  Resolve_scopes.unit_ list ->
  unit
(** Checks the macros that the modules declare, each in its module's scope, and
    records them in the state of [env]: their patterns (E0220) and templates
    (E0221), whether each template is an expression or a pattern, with each
    fragment standing as a form of its kind, and the names it writes, which
    resolve there (E0211). A macro with any of these errors reports nothing
    where it is used. A module that declares a macro is in the advanced tier. *)
