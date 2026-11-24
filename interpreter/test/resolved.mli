(** The resolved tree of a single-file test program, and what the names in its
    body refer to. *)

open Stilt

val fn_t : string -> Hir.fn_decl
(** The function [t] of the single-file program [text]. *)

val final_expr : Hir.fn_decl -> Hir.expr
(** The final expression of a function's body. *)

val show : Hir.expr -> string
(** What an expression refers to, such as [local x] or [fn std.fs.read]. *)

val refers : string -> unit
(** Prints what the final expression of [t]'s body refers to. *)
