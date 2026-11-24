(** The operations that can overflow (numbers.integer-panics and numbers.shifts;
    effects.overflow-effect): integer [+], [-] and [*], their compound
    assignments, [-] on a value that isn't a literal, [/] and [%] on a signed
    type unless the divisor is a literal other than [-1], and a shift unless its
    amount is a literal below the left operand's width. Wrapping operators
    can't. A call of [div_euclid] or [rem_euclid] by a literal names no native
    (std.integers), so its overflow by [-1] is its own. *)

val stmt : Tast.stmt -> (string * Ast.loc) list
(** The overflow of a compound assignment, as [s += x], if it can. *)

val expr : Tast.expr -> (string * Ast.loc) list
(** The overflow of an operator, as [a + b] or [-a]. *)
