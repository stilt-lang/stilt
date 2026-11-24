(** The natives of std that the calculus writes in its own terms. *)

val read_line : Model_types.cx -> Tast.expr -> Model_json.t
(** [io.read_line()] or [io.poll_line()], the call [e]: the line the input
    starts with, taken from it, or [None] at its end. *)

val read_all : Model_types.cx -> Tast.expr -> Model_json.t
(** [io.read_all()], the call [e]: the rest of the input, taken from it. *)

val option_native :
  Model_types.cx -> Tast.expr -> string -> Model_json.t list -> Model_json.t
(** [s.find(sub)], [s.rfind(sub)], [str.from_utf8(bytes)] or
    [str.from_code_point(p)], the call [e], by its name and exported operands.
*)

val strip :
  Model_types.cx -> Tast.expr -> string -> Model_json.t list -> Model_json.t
(** [s.strip_prefix(p)] or [s.strip_suffix(p)], the call [e], by its name and
    exported operands. *)

val optional_natives : string list
(** The natives of [str] that give an [Option], which {!optional} exports. *)

val optional :
  Model_types.cx -> Tast.expr -> string -> Model_json.t list -> Model_json.t
(** A call [e] of one of {!optional_natives}, by its name and exported operands.
*)

val int_optional :
  Model_types.cx ->
  Tast.expr ->
  string ->
  string ->
  Model_json.t list ->
  Model_json.t
(** A call [e] of an integer type's native that gives an [Option], by the type's
    name, the native's and its exported operands. *)

val int_optional_native : string -> Types.ty -> bool
(** Whether a native of an integer type, by its name and the call's type, is one
    {!int_optional} exports. *)

val parse : Model_types.cx -> Tast.expr -> Model_json.t -> Model_json.t
(** [s.to_T()], the call [e], for a numeric type [T], of the exported string
    [s]. *)

val panicking : (string * string) list
(** The prelude's functions that panic, by name, with the kind each panics with.
*)

val gives_option : Hir.item -> string -> Types.ty -> bool
(** Whether a native of std, by its owner, its name and the call's type, gives
    an [Option] that {!option_call} exports. *)

val option_call :
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  string ->
  Model_json.t list ->
  Model_json.t
(** A call [e] of a native that {!gives_option}, of its exported operands. *)

val std_call :
  Model_types.cx ->
  Tast.expr ->
  Hir.item ->
  (unit -> Model_json.t list) ->
  Model_json.t option
(** A call [e] of a native of std that the calculus writes in its own terms, of
    its operands exported by the function given: the writes of the output and
    standard error, [io.flush], the reads of the input, [cli.args] and the
    prelude's functions that panic. [None] for any other function. *)
