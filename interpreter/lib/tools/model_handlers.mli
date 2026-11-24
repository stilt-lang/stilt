(** Effects and handlers as the Lean model's calculus writes them: a
    performance, a handler literal, a [with] and a [resume]. *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

val perform :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  string ->
  Types.ty list ->
  Tast.arg list ->
  Model_json.t
(** [E.op(args)], with the effect's arguments. *)

val form : callbacks -> Model_types.cx -> Tast.expr -> Model_json.t
(** A handler literal, the record of its operations' bodies; [with h { block }];
    or [resume(v)], a performance of the reserved operation. *)
