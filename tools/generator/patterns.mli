(** Matches: a value to match on, the patterns that cover it, and [match]
    expressions. *)

val scrutinee :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  Code.code * (string * Context.var list) list
(** A value to match on, and patterns that cover it, each with the variables it
    binds. A guarded arm, which covers nothing for exhaustiveness
    (patterns.guards), may come first. *)

val match_expr :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  known:bool ->
  Ty.t ->
  Code.code
(** A [match] whose arms have type [ty], made by [expr] one level down. *)
