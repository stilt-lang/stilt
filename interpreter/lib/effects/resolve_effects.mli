(** Effects and handlers (handlers.declaring-effect, handlers.handler-literals
    and handlers.advanced-tier; tasks.async). *)

open Resolve_context

val resolve_effect : ctx -> public:bool -> Ast.effect_decl -> Hir.effect_decl
(** An effect, whose type parameters are in scope in its operations, each named
    once (E0208) and taking no [self] (E0215). Declaring one makes the module
    advanced (handlers.advanced-tier). *)

val resolve_handler :
  ctx ->
  block:(ctx -> Ast.block -> Hir.block) ->
  Hir.loc ->
  Ast.effect_ref ->
  Ast.ty option ->
  Ast.fn_decl list ->
  Hir.expr_desc
(** A handler literal at [loc], whose operations' bodies [block] resolves.
    Writing one makes the module advanced. *)
