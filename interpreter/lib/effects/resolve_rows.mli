(** Written effect rows (effects.rows), the effects they hold
    (handlers.effects-in-rows; tasks.async), and handler types
    (handlers.handler-types). [ty] resolves the types they hold. *)

open Resolve_context

val implicit_effects : string list
(** The implicit effects, which no row writes (facts.implicit-effects). *)

val check_public : ctx -> Hir.loc -> Hir.item -> entry -> unit
(** E0214 for a private item in a signature that other modules see
    (program.private-in-signatures). *)

val effect_ref :
  ctx ->
  ty:(ctx -> Ast.ty -> Hir.ty) ->
  Ast.effect_ref ->
  Hir.effect_inst option
(** The effect that a handler names, with its arguments, or [None] after an
    error: a name that is no effect (E0212) or the wrong number of arguments
    (E0300). Naming one makes the module advanced (handlers.advanced-tier;
    tasks.advanced-tier). *)

val resolve_row : ctx -> ty:(ctx -> Ast.ty -> Hir.ty) -> Ast.row -> Hir.row
(** A row, which holds each kind of label once (E0500), no implicit effect
    (E0501, facts.implicit-effects), and one instance of each effect (E0515,
    handlers.effects-in-rows). *)

val handler_type :
  ctx ->
  ty:(ctx -> Ast.ty -> Hir.ty) ->
  Ast.effect_ref ->
  Ast.ty option ->
  Ast.row ->
  Hir.ty_desc
(** A handler's type (handlers.handler-types), which makes the module advanced.
*)
