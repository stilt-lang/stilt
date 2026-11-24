(** A [use] whose path names no namespace (program.what-use-binds): one that
    names an item of a module (E0230), or nothing (E0205). *)

val declared : Ast.module_ -> Resolve_context.Sset.t
(** The names of the items that a module declares, in either namespace: its
    functions, constants, types and their variants, traits, effects and macros.
    A [use] declares no item of its module. *)

val missing :
  Resolve_context.env ->
  file:string ->
  package:int ->
  meta:bool ->
  Hir.loc ->
  Hir.name list ->
  unit
(** Reports the [use], or with [meta] the [meta use], at [loc] of a module of
    the package [package], whose path names no namespace: E0230 when, read as a
    path in code is, it names an item of a module, the first along it whose next
    name the module declares, and E0205 otherwise. *)
