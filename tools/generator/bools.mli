(** The forms that make a [bool]: comparisons, logic, and the methods that test
    a value. *)

val cond :
  Context.expr -> Context.body -> Context.scope -> depth:int -> Code.code
(** A [bool] whose type is fixed without an expected type. *)

val bool_ops :
  Context.expr -> Context.body -> Context.scope -> depth:int -> Context.forms
(** The forms that make a [bool] out of other values, whose operands [expr]
    makes one level down. *)
