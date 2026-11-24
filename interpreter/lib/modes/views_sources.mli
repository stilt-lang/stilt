(** The sources of views (views.making-view, views.across-calls and
    views.fixed): the places that a view, or a closure that captures one, reads.
    The analysis is lexical, as the durations of modes.durations are. *)

(** What a view reads: a place (modes.places), or a temporary that lasts as long
    as the view, made by the expression at a location (views.making-view); or
    what it writes, a place it was made from through [inout]
    (projections.what-view-writes). *)
type source =
  | Place of Modes_places.place
  | Written of Modes_places.place
  | Temporary of Ast.loc

type binding = {
  sources : source list;
  closure : Ast.loc option;
      (** The closure literal it holds, when it holds one that captures a view
          (traits.advanced-tier). *)
  writable : bool;
      (** Whether it is a [var] binding of [View<T>], a source in its own right
          (projections.writable-bindings and projections.places-through-views).
      *)
}
(** A variable that holds a view, or a closure that captures one. *)

type t = (int, binding) Hashtbl.t
(** The variables of a body that hold views, by [id]. *)

val collect : Tast.block -> t
(** The variables of a body that hold views, each with the sources of every
    value bound or assigned to it. *)

val sources : t -> Tast.expr -> source list
(** The sources of a value: a view's (views.making-view), a call's result's,
    which views every argument whose type is viewable or a view type
    (views.across-calls), a closure literal's, which are those of the views it
    captures (views.fixed), and for every other value none. A view parameter's
    sources are its argument's, which its body knows only as the parameter. *)

val argument : t -> Tast.arg -> source list
(** The sources that an argument gives the result of a call that returns a view
    (views.across-calls): the place it is, which the result writes when it is
    passed [inout] (projections.what-view-writes); a temporary for a viewable
    value that is no place; and the sources of a view or a closure. *)

val carries : t -> Tast.expr -> bool
(** Whether a value is a view, or a closure that captures one
    (views.view-types). *)

val closure : t -> Tast.expr -> Ast.loc option
(** The closure literal that captures a view, which a value is or holds. *)

val bound_in : Tast.expr -> int list
(** The variables bound inside an expression, by its patterns and by the
    parameters of the closures in it. *)

val reads : source -> bool
(** Whether a view reads the source: a place it views or a temporary, as against
    a place it writes (projections.what-view-writes). *)

val describe : source -> string
(** A source, for messages. *)

val describe_bare : source -> string
(** A source as a place is written, without quotes, for a fix. *)
