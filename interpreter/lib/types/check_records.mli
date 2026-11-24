(** Anonymous record literals, and updates of records
    (records.anonymous-literals and records.update). *)

val anonymous_literal :
  Check_state.ctx ->
  Types.ty option ->
  Ast.loc ->
  Hir.field_init list ->
  Tast.expr
(** [{ f: e, g }], of the anonymous record type of its fields, each named once
    (E0316), and never of a declared record's type (records.anonymous-literals).
    An expected anonymous record type gives the fields it names their types. *)

val named_update :
  Check_state.ctx ->
  Ast.loc ->
  Hir.ty ->
  Hir.expr ->
  Hir.field_init list ->
  Tast.expr
(** [Name { ..base, f: e }]: a record of the base's type, [Name<…>], with the
    fields written in place of its own, each one of the type's (E0313), at most
    once (E0316), with its type (E0311). *)

val anonymous_update :
  Check_state.ctx -> Ast.loc -> Hir.expr -> Hir.field_init list -> Tast.expr
(** [{ ..base, f: e }], for a base of an anonymous record type or of a type
    parameter with a record bound, whose bound's fields are the ones it may
    write. A declared record's update names it (E0311). *)
