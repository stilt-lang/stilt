(** Operators, and the types they are defined on
    (numbers.no-implicit-conversions and numbers.comparisons). *)

val integer_name : Types.ty -> string option
(** The name of an integer type, such as [Some "u8"]. *)

val supports : Types.ty -> Check_state.rule -> bool option
(** Whether a type supports an operator, or [None] while the type is open. *)

val unsupported :
  Check_state.state -> Types.ty -> Check_state.rule -> Ast.loc -> unit
(** Reports an operator that a type doesn't support. *)

val operator :
  Check_state.state -> Types.ty -> Check_state.rule -> Ast.loc -> Types.ty
(** The type of an operator's result, which is the type of its operands. An
    operator that the type doesn't support is an error, and its result then has
    the error type (errors.error-type). While the type is open, the check waits
    for the end of the body. *)

val not_an_amount : Check_state.state -> Types.ty -> Ast.loc -> unit
(** Reports a shift amount of a type that isn't an integer type
    (numbers.shift-amounts). *)

val amount_of : Check_state.ctx -> Types.ty -> Hir.expr -> Tast.expr
(** The amount by which a place of the type shifts, as [<<=] and [>>=] check it:
    with no expected type, and an integer type unless no shift is defined on the
    place's type (numbers.shifts; numbers.shift-amounts). *)

val binary :
  Check_state.ctx -> Ast.loc -> Ast.binary -> Hir.expr -> Hir.expr -> Tast.expr
(** A binary operator applied to its operands, which have one type
    (numbers.no-implicit-conversions and numbers.comparisons), but for a shift,
    whose amount has an integer type of its own (numbers.shifts and
    numbers.shift-amounts). *)
