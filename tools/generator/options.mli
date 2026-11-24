(** The forms that make an [Option]: lookups, the methods of options, fields
    read through an option, and conversions that can fail. *)

val option_ops :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  Ty.t ->
  Context.forms
(** The forms that make an [Option<t>] out of other values, whose operands
    [expr] makes one level down. *)
