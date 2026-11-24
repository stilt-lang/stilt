(** Records in the Lean model's calculus beyond their literals and fields. *)

val update :
  expr:(Tast.expr -> Model_json.t) ->
  Model_types.cx ->
  Tast.expr ->
  Tast.expr ->
  (string * Tast.expr) list ->
  Model_json.t
(** [update ~expr cx e base written]: the update [e], [{ ..base, f: x }], as
    [base] read into a temporary, then each field written, in order, then the
    record of [base]'s type with those fields and [base]'s others
    (records.update). *)
