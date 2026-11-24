(** The declarations of procedural macros (macros.procedural-declarations). *)

val check_decl : Resolve_context.ctx -> Ast.fn_decl -> Hir.fn_decl -> unit
(** Checks a macro's declaration, resolved as a function's, against
    macros.procedural-declarations: E0228 at each part that breaks it. *)
