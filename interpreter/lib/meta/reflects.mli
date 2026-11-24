(** The functions that reflect, and the types they are given (meta.reflects and
    meta.types-without-shape). *)

type t
(** Which function reflects on which of its type parameters, with the guards and
    the chain of each need: an inferred fact (meta.reflects). *)

val infer : Env.t -> Tast.program -> t
(** The facts of every function of the program, a least fixed point over the
    calls that bodies make. *)

val errors :
  t ->
  Env.t ->
  file:string ->
  key:Implicit_names.key option ->
  own:Hir.var list ->
  Tast.block ->
  Diagnostic.t list
(** The E0350 of a body, which the item [key] is the body of, if any: at each
    call or name of a function that reflects, given a type without a shape, and
    where a function of a trait reflects on a type parameter that its callers
    can't see (meta.types-without-shape and meta.unseen-instantiations). *)
