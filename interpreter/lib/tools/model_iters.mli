(** Iterators in the Lean model's calculus: an [Iter<T>] is a record of the
    library, and each function of [impl<T> Iter<T>] a form, the call of the
    function the model declares for it (views.making-iterator, views.adapters
    and views.consumers). *)

val iter_item : Hir.item
(** [std.view]'s [Iter]. *)

val element : Types.ty -> Types.ty option
(** [Some t] for an iterator type [Iter<t>]. *)

val call :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t
(** [call ~expr cx e name args]: the call [e] of the function [name] of
    [impl<T> Iter<T>]. Any other is outside the model. *)

val view_call :
  Model_types.cx ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t list ->
  Model_json.t
(** [view_call cx e name args values]: [view.range], [view.of_map], [view.chars]
    and [view.bytes], on the exported [values] of [args]. *)

val loop :
  Model_types.cx ->
  Ast.loc ->
  Types.ty ->
  Model_json.t ->
  string ->
  Model_json.t ->
  Model_json.t
(** [loop cx loc t it x body]: a [for] over the iterator [it] of [t]s, which
    asks it for one element at a time, binds it to [x] and runs [body]
    (views.for-over-view). *)
