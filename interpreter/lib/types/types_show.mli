(** Types as a program would write them, for messages (types.mismatch). *)

val to_string : Types.ty -> string
(** The type as a program would write it: [List<i64>], [(i64, str)],
    [{ age: i64, name: str }] or [..List<Ts>]. *)

val effect_to_string : Hir.item * Types.ty list -> string
(** An effect with its type arguments, as a row writes it: [State<i64>]. *)
