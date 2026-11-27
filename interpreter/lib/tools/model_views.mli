(** Views in the Lean model's calculus, as the reference interpreter holds them:
    a view is the part it reads (views.what-view-is). *)

val view_item : Hir.item
(** [std.view]'s [View]. *)

val viewed : Types.ty -> Types.ty option
(** [Some t] for a view type [View<t>]. *)

val view : Model_json.t list -> Model_json.t
(** A view of its operands, the source first (views.making-view). *)

val desugar : Tast.expr -> Tast.expr
(** [e] with each view it reads as an operand of [v[i]], a [for], a splice or an
    operator read as the view's [copy()], which gives the viewed part: those
    forms read the part as the same forms of the part's type do
    (views.functions-of-views, views.for-over-view). *)

val call :
  expr:(Tast.expr -> Model_json.t) ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t
(** [call ~expr e name args]: the call [e] of the function [name] of
    [impl<T> View<T>]: [View.of], [View.all] and [view] as the calculus's view
    (views.making-view), [len], [is_empty] and [copy]
    (views.functions-of-views). Any other is outside the model. *)
