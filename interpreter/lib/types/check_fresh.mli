(** Fresh types (meta.fresh-types): the type of a field, an element or a payload
    is a fresh type of the arm or the loop body that reads it, and a value whose
    type holds one can't leave it (E0351). *)

val leaves :
  Check_state.state -> Ast.loc -> expected:Types.ty -> Types.ty -> bool
(** [leaves st loc ~expected actual] reports E0351 at [loc], and tells whether
    it did, where unification refused [actual] for [expected] only because a
    fresh type that one holds would decide a type that inference left open
    outside its arm. Against a type known outside, a fresh type is a mismatch,
    which this leaves to E0311. *)

val arm_value : Check_state.state -> int -> Tast.expr -> Tast.expr
(** [arm_value st mark body] is the value of an arm, or of an [if let]'s first
    branch, that decides its form's type: with E0351 and the error type when its
    type holds a fresh type made after [mark]. *)

val raised : Check_state.state -> Tast.expr -> bool
(** Whether a raised value may leave its arm: E0351, and [false], when its type
    holds a fresh type. *)
