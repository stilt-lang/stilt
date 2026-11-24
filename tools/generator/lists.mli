(** The forms that make a list: the methods of other lists, the pieces of a
    string, and lists of pairs. *)

val list_ops :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  Ty.t ->
  Context.forms
(** The forms that make a list of [t] out of other values, whose operands [expr]
    makes one level down. *)
