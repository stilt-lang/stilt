(** The operators of a program, and the natives of the standard library that the
    Lean model's calculus has as operations, over operands already exported. *)

val op : Model_json.t -> Model_json.t list -> Model_json.t
(** An operation applied to its operands. *)

val str_lit : string -> Model_json.t

val int_lit : Types.ty -> string -> negated:bool -> Model_json.t
(** An integer literal of its type, as written, negated by a [-] before it. *)

val literal_value : string -> string -> string
(** [literal_value kind text] is the value of an integer literal of the type
    [kind], or of a negative literal pattern, whose text starts with [-]. *)

val unary : Ast.unary -> Types.ty -> Model_json.t -> Model_json.t

val binary_at :
  Model_types.cx ->
  Ast.binary ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [binary], with [==] and [!=] on maps whose keys and values the calculus
    compares part by part. *)

val binary :
  Ast.binary ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** The operator on operands of the types given. [&&] and [||] are [if]s. *)

val native : Hir.item -> string -> Types.ty -> Model_json.t list -> Model_json.t
(** A call of a native member of [str] or of an integer type, by its owner, its
    name and its result type. *)

val decimal_at_float : Types.ty -> string -> bool
(** Whether an integer literal written in decimal stands at a float type, where
    it means the float literal of its digits (numbers.integer-literals). *)

val float_lit : Types.ty -> string -> Model_json.t
(** A float literal as written, of the float type its context expects
    (numbers.float-literals): its digits and decimal exponent. *)

val int_float : Types.ty -> string -> Model_json.t
(** An integer literal written in decimal at a float type: the calculus's form
    of it, the float literal of its value (numbers.integer-literals). *)

val cmp : Ast.binary -> string option
(** The calculus's name of a comparison operator. *)

val formatted :
  shown:(unit -> Model_json.t) ->
  Types.ty ->
  string ->
  Model_json.t ->
  Model_json.t
(** A splice of [x] with a format spec, its text given by the spec, or by
    [shown] when the spec gives no precision or kind for its type. *)

val show : structural:bool -> Types.ty -> Model_json.t -> Model_json.t
(** A value interpolated into a string (std.show-output): of another type than
    an integer type, [bool] and [str], only when [structural] says the prelude's
    structural impls of [Show] show it. *)
