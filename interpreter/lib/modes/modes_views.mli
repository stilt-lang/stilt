(** The reads that views make (views.reads-that-last, views.change-while-viewed
    and views.for-over-view), which the law of exclusivity weighs with a body's
    other accesses (modes.law). Reads are lexical: each lasts until the end of a
    scope, which the walk of the body opens and closes in source order. *)

type read = {
  place : Modes_places.place;  (** A source of the view. *)
  view : string;  (** The view, for messages. *)
  until : int Lazy.t;
      (** The last line of code that the read lasts for, which only a message
          needs. *)
  scope : int;  (** The scope whose end ends it. *)
  writes : bool;
      (** Whether a writable binding writes the place, which no access may reach
          (projections.what-view-writes). *)
}

type t = private {
  sources : Views_sources.t;
  mutable live : read list;  (** The reads in progress. *)
  mutable next : int;
  bindings : (int, int * int Lazy.t) Hashtbl.t;
      (** The scope and last line of each binding that holds a view, by [id]. *)
}

val create : Tast.block -> t
(** The reads of a body, none in progress. *)

val scope : t -> int
(** A new scope. *)

val close : t -> int -> unit
(** Ends the reads that last until the end of a scope. *)

val last_line : Tast.expr list -> int Lazy.t
(** The last line that holds code of the expressions. *)

val stmt_last : Tast.stmt -> int Lazy.t
(** The last line that holds code of a statement. *)

val block_last : Tast.block -> int Lazy.t
(** The last line that holds code of a block. *)

val made : t -> int * int Lazy.t -> Tast.expr -> unit
(** [made t (scope, until) e] begins the reads of the view that the call [e]
    returns, if it returns one, which last until the end of the statement that
    holds it: [scope], whose last line is [until] (projections.writable-views).
*)

val operand : t -> int * int Lazy.t -> Tast.expr -> Tast.arg -> unit
(** [operand t (scope, until) e a] begins the reads of the sources that the
    [let] argument [a], just evaluated, gives the view that the call [e]
    returns, if it returns one: a later argument may not change them
    (views.reads-that-last and views.change-while-viewed). They last as [made]'s
    do. *)

val bound : t -> scope:int -> until:int Lazy.t -> Tast.stmt -> unit
(** Begins the reads of the views that a statement binds, which last for their
    bindings' scope, [scope], whose last line is [until], or of the view that it
    assigns to a binding that holds one, which last for that binding's scope
    (projections.writable-views and projections.writable-bindings). *)

val conflict : ?writing:bool -> t -> Modes_places.place -> read option
(** A write in progress of a place that overlaps [p], which any access of [p]
    breaks (projections.what-view-writes), or, when the access is a
    modification, [writing], a read in progress of one, which it breaks
    (projections.what-view-writes). *)
