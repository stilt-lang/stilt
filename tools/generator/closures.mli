(** Closures, whose bodies read copies of the variables in scope. *)

val fold :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  Ty.t ->
  Code.code
(** [xs.fold(init, |acc, x| body)], whose accumulator has type [ty]. *)

val closure :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  ?known:bool ->
  Ty.t ->
  Ty.t ->
  string
(** A closure of one parameter of type [param], whose body has type [ty]. A body
    whose type nothing else fixes, as [map]'s, is [~known]. *)
