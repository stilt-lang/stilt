(** The uses of procedural macros, run as names are resolved (macros.meta-use,
    macros.procedural-uses and macros.running). *)

open Resolve_context

(** What a use's path names. *)
type found =
  | Proc of Hir.item * Procs.state
      (** A procedural macro of a module named with [meta use]. *)
  | Missing
      (** Nothing, through a [meta use] that names no such macro, which is
          reported. *)
  | Not_proc  (** No procedural macro: a pattern macro's path, or none. *)

val find : ctx -> Ast.path -> found
(** What [m.name], a use's path, names when [m] is bound by a [meta use]: one of
    its procedural macros, which must be public (E0213), and nothing else of the
    module (E0211) unless a [use] binds [m] too (macros.meta-use). *)

val names_proc : ctx -> Ast.path -> bool
(** Whether a use's path names a procedural macro, as {!find} reads it, without
    reporting anything. *)

val run :
  ctx ->
  Ast.loc ->
  Hir.item ->
  Procs.signature ->
  Ast.tree list ->
  Lexer.token list option
(** [run ctx loc item signature groups] runs the macro [item] on the parts of
    the use at [loc] whose groups are [groups], giving its expansion, or [None]
    after E0227 for parts that don't fit its parameters, E0229 for a file that
    can't be given, E0225 for an error the macro raised and E0226 for a run that
    didn't finish. *)
