(** Values built from literals and constructors, of every type. *)

val value :
  Context.expr ->
  Context.body ->
  Context.scope ->
  depth:int ->
  known:bool ->
  Ty.t ->
  Code.code
(** A value of type [ty], whose parts [expr] makes one level down. An integer
    literal whose type must be known is a constant, or an [i64] converted with a
    wrapping conversion, since a literal takes its type from the context and
    defaults to [i64] (numbers.literal-defaults). *)
