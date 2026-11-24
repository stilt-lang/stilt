(** Places (modes.places), and the variables code binds and may modify. *)

(** A step from a place to a part of it. An index is kept only as a position. *)
type step = Field of string | Index

type place = { root : Hir.var; path : step list }

val place : Tast.expr -> place option
(** The place an expression names, if it names one. *)

val overlap : place -> place -> bool
(** Whether two places can share a part (modes.overlap), counting the names of a
    [when] whose values have the same type as one
    (shared.names-that-may-be-one-place). *)

val holding : (Hir.var * Tast.ty) list -> (unit -> 'a) -> 'a
(** [holding names check] runs [check] with the names of a [when], each with its
    value's type, counted as one where their types are the same
    (shared.names-that-may-be-one-place). *)

val place_parts : Tast.expr -> Tast.expr list
(** The expressions that a place evaluates to find its target, which are its
    indexes, in order. *)

val pattern_vars : Tast.pattern -> int list
(** The variables a pattern binds. *)

val var_bindings : Tast.block -> int list
(** The variables a body declares with [var], outside the closures in it
    (modes.what-can-be-modified). *)

val expr_var_bindings : Tast.expr -> int list
(** [var_bindings] of the blocks inside an expression. *)

val inout_params : (Ast.mode * 'a) list -> 'a list
(** The [inout] parameters among a body's parameters. *)
