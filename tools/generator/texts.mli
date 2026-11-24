(** The forms that make a [str]: interpolations, with their format specs, and
    the methods of strings. Each takes [expr], which makes its operands. *)

val interpolation :
  Context.expr -> Context.body -> Context.scope -> depth:int -> Code.code
(** An interpolated string, whose splices have types fixed in their body
    (std.invalid-specs), with the format specs std.invalid-specs allows them. *)

val str_ops :
  Context.expr -> Context.body -> Context.scope -> depth:int -> Context.forms
(** The forms that make a [str] out of other values, one level down. *)
