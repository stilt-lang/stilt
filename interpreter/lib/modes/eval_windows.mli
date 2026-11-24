(** Writable views (projections.writable-views, projections.what-view-writes and
    projections.places-through-views): windows into the part of a list that a
    place of a frame holds, which a write through the view writes. *)

val thaw : Eval_state.t -> Eval_state.frame -> Value.value -> Value.value
(** The part a window views, as a value of its own; any other value itself. *)

val into :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Eval_state.frame * Eval_places.place ->
  Value.value ->
  Value.value ->
  Value.value
(** [into t fr loc (wfr, place) start stop] is [view.into(inout xs, start, end)]
    for the list at [place] in the frame [wfr]: a window into its part, which
    panics at [loc] with [bounds] as [View.of] does
    (projections.writable-views). *)

val part :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Eval_state.frame * Eval_places.place ->
  Value.value ->
  Value.value ->
  Value.value
(** [view.part(inout v, start, end)] for the window at the place: a window into
    its part, with offsets counted from its start (projections.writable-views).
*)

val halves :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  Eval_state.frame * Eval_places.place ->
  Value.value ->
  Value.value * Value.value
(** The two windows that [view.split(inout xs, at, f)] calls [f] with: the parts
    of the list at the place before and from [at] (projections.writable-views).
*)

val native :
  Eval_state.t ->
  Eval_state.frame ->
  Ast.loc ->
  opened:
    ('p -> (Eval_state.frame * Eval_places.place -> Value.value) -> Value.value) ->
  call:(Value.value -> Value.value -> Value.value -> Value.value) ->
  string ->
  (Value.value, 'p) Either.t list ->
  Value.value
(** [native t fr loc ~opened ~call name args] runs [view.into], [view.part] or
    [view.split] (projections.writable-views) on its arguments, of which the
    [inout] ones are places that [opened] opens, and calls the closure of
    [split] on its two windows with [call]. *)

val retarget :
  callee:Eval_state.frame ->
  (int * (Eval_state.frame * Eval_places.place)) list ->
  Value.value ->
  Value.value
(** [retarget ~callee places v] gives the windows of a value that a call
    returns, which write an [inout] parameter of [callee], the caller's argument
    for it to write instead: [places] gives, by the parameter's variable, the
    caller's frame and place (projections.what-view-writes and
    projections.reaching-written-source). *)

val copied :
  target:Eval_state.target ->
  accesses:(Value.value, Eval_state.frame * Eval_places.place) Either.t list ->
  Eval_state.frame ->
  Value.value ->
  Value.value
(** [copied ~target ~accesses pfr v] gives the windows of [v], a value copied
    out of a place of the frame [pfr] that the projection [target] yielded,
    which write an [inout] parameter of the projection, the caller's argument
    for it to write instead: [accesses] gives the caller's arguments, the value
    of each [let] one and the frame and place of each [inout] one
    (projections.call-is-place). *)
