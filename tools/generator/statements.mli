(** Statements, and the blocks they make. A block's bindings end with it, and
    every loop runs a bounded number of times. *)

val stmts :
  Context.body ->
  Context.scope ->
  depth:int ->
  int ->
  Context.scope * Code.line list
(** [n] statements, at most [depth] levels deep, and the scope after them. *)
