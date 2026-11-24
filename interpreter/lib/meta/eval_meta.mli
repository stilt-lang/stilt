(** Reflection at run time (meta.shapes and meta.fresh-types): the shapes of the
    concrete types that a body's type arguments give, bound tests, and the fresh
    types that arms and loops bind. *)

val reflect : Eval_state.t -> Eval_state.frame -> Tast.reflect -> Value.value
(** A type's shape or name, or a bound test, for the frame's types. *)

val bind_case :
  Eval_state.t ->
  Eval_state.frame ->
  Types.ty ->
  Hir.item ->
  Tast.pattern list ->
  unit
(** [bind_case t fr shape case ps]: the pattern of [case], a case of the type
    [shape], a [Shape<T>], with payload patterns [ps], binds the fresh types
    that [ps] hold to the types that [T] holds, in the frame (meta.fresh-types).
*)

val iterated : Types.ty -> bool
(** Whether a [for] over a value of this concrete type iterates fields or cases
    (meta.fields and meta.variant-cases). *)

val iterate :
  Eval_state.t ->
  Eval_state.frame ->
  Types.ty ->
  Tast.pattern ->
  (Value.value -> bool) ->
  unit
(** [iterate t fr ty p each] runs [each] on each field of a [meta.Fields<T>], or
    each case of a [meta.Cases<T>], in order, with the fresh type that [p]'s
    type holds bound to the field's type or the payload's, until [each] tells to
    stop. *)

val fields : Eval_state.t -> Types.ty -> (string * Types.ty) list
(** The fields of a tuple or a record type, in order (meta.shapes). *)

val variants : Eval_state.t -> Types.ty -> (Hir.item * Types.ty list) list
(** The variants of a variant type, in order, with their payloads' types. *)
