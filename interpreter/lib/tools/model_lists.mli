(** The natives of lists and maps in the Lean model's calculus (std.lists and
    std.maps): each a function of the calculus, a list or a map a value, so one
    that changes its receiver writes its result back to the receiver's place. *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;  (** Exports an expression. *)
  stored :
    Tast.expr ->
    Tast.expr list ->
    (Model_json.t -> Model_json.t list -> Model_json.t) ->
    Model_json.t;
      (** [stored target operands make] stores [make read operands] into the
          place [target], its index expressions and the operands evaluated once,
          in order (values.compound-assignment-order). *)
}

val map_call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t
(** [map_call on cx e name args]: the call [e] of [Map]'s function [name] on its
    arguments, the receiver first. *)

val set_call : callbacks -> string -> Tast.arg list -> Model_json.t
(** [set_call on name args]: a call of [Set]'s function [name] on its arguments,
    the receiver first. *)

val set_natives : string list
(** The functions of [Set] that {!set_call} writes; the others run their code.
*)

val map_natives : string list
(** The functions of [Map] that {!map_call} writes; the others run their code.
*)

val natives : string list
(** The functions of [List] that {!list_call} writes. *)

val list_call :
  callbacks ->
  Model_types.cx ->
  Tast.expr ->
  string ->
  Tast.arg list ->
  Model_json.t
(** A call of [List]'s native [name], the call's expression [e] given for its
    type and its place in the source. *)

val array_fill :
  callbacks -> Model_types.cx -> Tast.expr -> Tast.expr -> Model_json.t
(** [array.fill(x)], the call [e]: the list of [n] copies of [x], or a [bounds]
    panic. *)

val array_from_list :
  callbacks -> Model_types.cx -> Tast.expr -> Tast.expr -> Model_json.t
(** [array.from_list(xs)], the call [e]: [Some] of [xs] when its length is the
    array's. *)
