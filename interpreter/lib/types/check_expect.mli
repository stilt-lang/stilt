(** Expected types: requiring a type to be the one expected, and checking an
    expression against one (types.expected-types and types.mismatch). *)

val agrees :
  Check_state.state -> Ast.loc -> expected:Types.ty -> Types.ty -> bool
(** Requires [actual] to be [expected], and tells whether it is. *)

val expect :
  Check_state.state -> Ast.loc -> expected:Types.ty -> Types.ty -> unit
(** [agrees], reporting only. *)

val fits : Check_state.state -> Ast.loc -> expected:Types.ty -> Types.ty -> bool
(** Requires a value of type [actual] to be usable where [expected] is, and
    tells whether it is: a value of type [Never] fits anywhere, and a function
    fits where a function type with a larger row is expected
    (declarations.never; effects.function-value-unions). *)

val subsume :
  Check_state.state -> Ast.loc -> expected:Types.ty -> Types.ty -> unit
(** [fits], reporting only. *)

val widen : Types.ty -> Types.ty
(** A type that values of type [t] fit in, whose function row may grow to hold
    the rows of other function values (effects.function-value-unions). *)

val known : Check_state.state -> Ast.loc -> Types.ty -> Types.ty option
(** A type that must be known where it is used, as a receiver's is
    (traits.method-resolution), or [None] after reporting that it isn't. A
    literal's type takes its default there (numbers.literal-defaults). *)

val instantiated :
  Check_state.state -> Types.ty option -> Tast.expr -> Tast.expr
(** A value of a polymorphic function type, used where none is expected,
    instantiated afresh: its type parameters take fresh variables, which meet
    their bounds there (polymorphism.instantiation). Any other value is itself.
*)

val infer : Check_state.ctx -> Types.ty option -> Hir.expr -> Tast.expr
(** Infers the type of an expression, as [Check_exprs.infer] does, checking it
    against the expected type where there is one. *)

val check_fits : Check_state.ctx -> Types.ty -> Hir.expr -> Tast.expr * bool
(** [check], telling whether the expression fits the expected type. Where a
    polymorphic function type is expected, a generic function named as a value
    or a closure literal is checked with a rigid type for each of its type
    parameters, and any other expression must have that type
    (polymorphism.rigid-types). *)

val check : Check_state.ctx -> Types.ty -> Hir.expr -> Tast.expr
(** Checks an expression against an expected type. *)

val abandon : Check_state.ctx -> Hir.expr -> Tast.expr
(** Checks an expression whose expected type an error hides, as the error type,
    so that it causes no error of its own (errors.error-type). *)

val infer_checked : Check_state.ctx -> Types.ty option -> Hir.expr -> Tast.expr
(** Checks an expression against an expected type when there is one. *)

val settled : Check_state.state -> Types.ty -> Ast.loc -> Types.ty option
(** The type that the first branch of an [if], a [match] or a [try … catch]
    whose type isn't expected gives the later branches, which are checked
    against it (expressions.if). A function type's row grows to hold theirs
    (effects.function-value-unions). [None] while every branch so far has type
    [Never]. *)
