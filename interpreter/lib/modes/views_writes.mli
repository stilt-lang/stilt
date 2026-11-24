(** Views that must write (projections.yield and projections.writable-bindings):
    the view given to a [var] binding of [View<T>], assigned to the whole of
    one, or yielded by a projection without being a place, writes every source
    it has. A view that reads one is E0428, at the view. *)

val stmt :
  Views_sources.t -> (Code.t -> Ast.loc -> string -> unit) -> Tast.stmt -> unit
(** The errors of a statement, reported through the function given. *)
