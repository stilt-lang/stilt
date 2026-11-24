(** The types of views (views.viewable-types and views.view-types): the types
    that can be viewed, the view types, and where a view type may stand. *)

val is_view_con : Hir.item -> bool
(** Whether a type constructor is [View] or [Iter] of [std.view]. *)

val viewable : Types.ty -> bool
(** Whether a type can be viewed: [str] or a [List] (views.viewable-types). *)

val is_view : Types.ty -> bool
(** Whether a type is a view type that its type shows: [View<T>], [Iter<T>], or
    [Option<V>] for a view type [V] (views.view-types). A closure that captures
    a view is one too, which its type doesn't show (views.fixed). *)

val stores : Types.ty -> bool
(** Whether a type holds a view type where views.view-types allows none: as a
    field or a payload other than [Option]'s, an element of a [List] or a [Map],
    a component of a tuple, or a type argument of a declared type. *)

val is_window : Types.ty -> bool
(** Whether a type is [View<T>] itself, which a [var] binding or an [inout]
    parameter of it writes through (projections.writable-bindings and
    projections.places-through-views). *)

val written :
  (Code.t -> Ast.loc -> string -> unit) -> stored:bool -> Hir.ty -> unit
(** [written report ~stored t] reports, through [report code loc message], the
    E0420 of each [View] in the written type [t] whose argument can't be viewed,
    at the argument, and the E0421 of each view type that [t] holds where
    views.view-types allows none, at the view type. [stored] tells whether [t]
    itself stands where a value is stored, as a field's type does. *)

val declarations : Hir.program -> Diagnostic.t list
(** The E0420 and E0421 of the types written in the declarations of the
    program's modules: the fields and payloads of their types, the signatures of
    their functions, and the types of their constants. *)

val erase : Hir.program -> Hir.program
(** The program with each type that a declaration of its own modules writes with
    an error of views.viewable-types or 4 made the error type, as
    errors.declarations-with-errors makes each part of a signature with an
    error: a field's, a payload's, a constant's, and a parameter's, a result's
    or an error type of a function or an operation. *)
