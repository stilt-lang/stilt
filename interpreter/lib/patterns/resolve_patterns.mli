(** Patterns, and the names they bind (patterns.pattern-forms). *)

open Resolve_context

type binder = {
  mutable bound : (string * Hir.var) list;  (** Latest first. *)
  mutable broken : Sset.t;  (** Bound names whose uses have the error type. *)
  mutable partial : string list;
      (** Names that only some alternatives of an or-pattern bind. They bind
          nothing, but their uses have the error type unless the pattern binds
          them elsewhere (patterns.or-patterns). *)
  mutable failed : bool;
      (** Whether the pattern holds a failed use of a procedural macro, which
          binds nothing (macros.failed-uses). *)
  shared : (string * Hir.var) list;
      (** In an alternative of an or-pattern after the first, the variables of
          the first, which the same names bind again. *)
  checked : bool;
      (** Whether names are checked against the module's names here. Inside an
          alternative of an or-pattern they are checked once, when the
          or-pattern adds them to its own binder. *)
}
(** The names that a pattern binds, as it is resolved. *)

val binder : unit -> binder
(** A binder that binds nothing yet. *)

val with_bound : ctx -> binder -> ctx
(** The context with the names of [binder] in scope. After a failed use, a name
    that names nothing there has the error type and is reported nowhere
    (macros.failed-uses). *)

val bind : ctx -> binder -> Hir.name -> Hir.var
(** Binds a name, unless the pattern already binds it, which is an error. A name
    can't be a primitive type's (errors.primitive-type-bindings) or an imported
    module's (program.one-value-namespace). *)

val resolve_pattern : ctx -> binder -> Ast.pattern -> Hir.pattern
(** Resolves a pattern, binding its names in [binder]. *)
