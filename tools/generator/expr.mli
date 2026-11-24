(** Expressions. Each is made for the type its context expects: a variable, a
    field or a call that has the type, or one of the forms that make a value of
    the type out of others. *)

val expr : Context.expr
(** [expr b sc ~depth ~known ty] is an expression of type [ty], at most [depth]
    levels deep. With [~known:true], its type is fixed without an expected type.
*)

val handler : Context.body -> Context.scope -> depth:int -> Ty.t -> string
(** The arms of a [catch] of [Fault] whose bodies have type [ty]: a catch-all,
    which needs a reason (effects.catch-alls-need-reason), or an arm for each
    variant. *)

val cond : Context.body -> Context.scope -> depth:int -> Code.code
(** A [bool] whose type is fixed without an expected type. *)

val closure :
  Context.body ->
  Context.scope ->
  depth:int ->
  ?known:bool ->
  Ty.t ->
  Ty.t ->
  string
(** A closure of one parameter of type [param], whose body has type [ty]. A body
    whose type nothing else fixes, as [map]'s, is [~known]. *)

val interpolation : Context.body -> Context.scope -> depth:int -> Code.code
(** An interpolated string, whose splices have types fixed in their body
    (std.invalid-specs). *)

val scrutinee :
  Context.body ->
  Context.scope ->
  depth:int ->
  Code.code * (string * Context.var list) list
(** A value to match on, and patterns that cover it, each with the variables it
    binds. *)
