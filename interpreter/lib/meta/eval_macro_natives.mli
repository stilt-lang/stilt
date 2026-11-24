(** The natives of [std.meta] that macros use (macros.tokens-and-code and
    macros.cursor). Each performs nothing but the allocation of what it makes.
*)

val tokens : Macro_values.token list -> Macro_values.span -> Value.value
(** A [meta.Tokens] of [items], whose closing bracket is at [close]. *)

val method_ :
  Eval_state.frame ->
  Ast.loc ->
  string ->
  string ->
  Value.value array ->
  Value.value
(** Calls the native method [name] of the [std.meta] type [owner] on [args], the
    receiver first. *)

val function_ : Ast.loc -> string -> Value.value array -> Value.value
(** Calls the native function [name] of [std.meta] on [args]: [fresh], [error],
    and the parsers of a cursor. *)

val owners : string list
(** The owners of the methods of macros' values. *)
