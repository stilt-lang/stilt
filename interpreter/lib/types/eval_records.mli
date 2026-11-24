(** Records and tuples at run time: literals, reads of fields and elements,
    updates (records.anonymous-literals and records.update), and the values of
    spreads (variadics.spread-expressions). Each evaluates its parts with
    [expr]. *)

type eval = Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value

val field : Value.value -> string -> Value.value
val tuple_field : Value.value -> int -> Value.value

val record :
  expr:eval ->
  Eval_state.t ->
  Eval_state.frame ->
  Hir.item ->
  (string * Tast.expr) list ->
  Value.value
(** A record literal's fields, evaluated in the order they are written and
    stored in the declaration's order, or for an anonymous record in the
    alphabetical order of their names (records.field-order). *)

val update :
  expr:eval ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.expr ->
  (string * Tast.expr) list ->
  Value.value
(** The base, then the fields in written order, which replace the base's own
    (records.update). *)

val elements :
  expr:eval ->
  Eval_state.t ->
  Eval_state.frame ->
  Tast.expr list ->
  Value.value list
(** The values of a tuple's or a list's elements, or of a call's arguments, each
    spread's in its place: its body evaluated once for each element of its pack,
    in order, with each pack tuple it names bound to its element
    (variadics.spread-expressions). *)
