(** Reflection in type checking (meta.shape-and-name and meta.fresh-types):
    [T.shape()] and [T.name()], the fresh types of the arms and loops that read
    a shape, and bound tests. *)

val reflection :
  Check_state.state -> Types.ty -> Hir.name -> (Tast.reflect * Types.ty) option
(** [reflection st ty name] is [ty.shape] or [ty.name] of [std.meta], with the
    type it gives, in [std.meta] and in a module that names it with [use], where
    the type has no member [name] of its own (meta.shape-and-name). *)

val payload : Hir.item -> Types.ty list -> Types.ty list -> Types.ty list
(** [payload owner args payload] is the payload of a variant of [owner] with
    [args] in a pattern: for a case of [Shape<T>], with a fresh type of its own
    for each of [E], [K] and [V] (meta.shapes and meta.fresh-types). *)

val element : Types.ty -> Types.ty option
(** What [for] binds for each field of a [meta.Fields<T>] or each case of a
    [meta.Cases<T>], with a fresh type of the loop's body (meta.fields and
    meta.variant-cases). *)

val tested : Hir.var -> Hir.bound list -> Types.bound list
(** The bounds of a bound test on a type parameter, with their arguments
    (meta.bound-tests). *)

val within :
  Check_state.state -> Hir.var -> Types.bound list -> (unit -> 'a) -> 'a
(** [within st v bounds k] runs [k] with [bounds] added to those of [v], as the
    branch of a bound test is checked (meta.bound-tests). *)
