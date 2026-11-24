(** Statements that change variables in scope: assignments, changes to a field,
    a list or a map, and calls that pass variables [inout]. What a statement
    changes, its other parts don't read (modes.overlap). *)

val changes :
  Context.body ->
  Context.scope ->
  depth:int ->
  (int * (unit -> Context.scope * Code.line list)) list
(** The statements that change a variable in scope, each with its weight, as
    [Pick.run] takes them, and with the scope after it, which is [sc]. *)
