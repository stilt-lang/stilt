(** Fields: places, reads of fields, through an [Option] too
    (types.fields-through-option), and record literals. *)

val is_place : Hir.expr -> bool
(** Whether an expression is a variable, or a field or element of a place
    (expressions.places). *)

val through_option : Tast.expr -> bool
(** Whether the checked form of a place reads a field through an [Option], which
    makes it a copy rather than a place (types.option-field-not-place). *)

val may_be_place : Hir.expr -> bool
(** Whether an expression may be a place once checked: a place, or a call that
    may be a projection's, which only its callee decides
    (projections.call-is-place). *)

val rooted_in_projection : Tast.expr -> bool
(** Whether the checked form of an expression is a projection's call, or a
    field, an element or an index of one (projections.call-is-place). *)

val checked_place : Hir.expr -> Tast.expr -> bool
(** [checked_place e checked] tells whether [e], whose checked form is
    [checked], is a place (expressions.places; projections.call-is-place). *)

val record_fields :
  Check_state.state -> Types.ty -> (string * Types.ty) list option
(** The fields of a record type, with their types, or [None] if the type isn't a
    record's. *)

val field_access :
  Check_state.ctx -> Ast.loc -> Hir.expr -> Hir.name -> Tast.expr
(** A read of a field of a value, or of an element of a tuple. *)

val struct_literal :
  Check_state.ctx -> Ast.loc -> Hir.ty -> Hir.field_init list -> Tast.expr
(** A record literal, which gives every field of its type once. *)
