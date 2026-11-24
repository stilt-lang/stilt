(** Types at run time: the types of a body with its type arguments, the numeric
    types, the components of compound values, and the literals whose values
    their types decide (types.known-types). *)

val concrete : Eval_state.frame -> Types.ty -> Types.ty
(** A type with the frame's type arguments in place of its parameters. *)

val value_param : Eval_state.frame -> Hir.var -> Types.ty -> Value.value
(** [value_param fr v ty] is the value that the frame's type arguments give the
    value parameter [v] of type [ty] (generics.value-parameters-in-body). *)

val concrete_callee : Eval_state.frame -> Tast.callee -> Tast.callee
(** A callee whose type, for a trait method, is {!concrete}. *)

type numeric =
  | Integer of Ints.kind
  | Floating of bool
  | Not_numeric
      (** Whether a type is an integer type, or a float type, [f32] for [true].
      *)

val numeric : Types.ty -> numeric

val components :
  Eval_state.t -> Types.ty -> Value.value -> (Types.ty * Value.value) list
(** The components of a value of a type, in order, with their types: the
    elements of a tuple or a list, the payload of a variant, the fields of a
    record. *)

val viewed : Types.ty -> Types.ty
(** The type of the value of a value of a type: for a view, [View<T>], the type
    [T] of the part it views, which is its value (views.functions-of-views); for
    any other type, the type itself. *)

val key_value_types : Types.ty -> Types.ty * Types.ty
(** The key and value types of a map type. *)

val variant_index : Eval_state.t -> Hir.item -> int
(** The position of a variant in its type's declaration. *)

(** {1 Literals} *)

val int_literal : Types.ty -> string -> Value.value
(** An integer literal as written, of an integer or a float type. A float holds
    its value exactly (numbers.integer-literals). *)

val pattern_literal : string -> int64
(** An integer pattern's literal, whose [-] is part of it
    (numbers.negative-literals). *)

val negative_literal : Types.ty -> string -> Value.value
(** An integer literal after a [-], which makes a literal with its sign
    (numbers.negative-literals). *)

val float_literal : Types.ty -> string -> Value.value
(** A float literal as written, rounded to its type in one step. *)
