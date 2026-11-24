(** The forms that make an integer or a float: arithmetic, conversions, and the
    methods of numbers. Each takes [expr], which makes its operands one level
    down. *)

val int_ops :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  known:bool ->
  Ty.int_kind ->
  Context.forms
(** The forms that make an integer of kind [k] out of other values. Operands are
    masked so that the checked operators can't overflow, and divisors and shift
    amounts kept in range (numbers.integer-panics and numbers.shift-amounts). *)

val float_ops :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  known:bool ->
  Ty.float_kind ->
  Context.forms
(** The forms that make a float of kind [k] out of other values. *)
