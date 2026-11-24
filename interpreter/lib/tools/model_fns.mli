(** The functions an export reaches, each at the type and row arguments it is
    called with: a generic function is declared once for each, its body with its
    parameters replaced by them. *)

val target_name : Model_types.target -> string

val signature : Model_types.cx -> Model_types.target -> Env.fn_sig
(** The function's signature; raises {!Model_types.Outside} for none. *)

val code :
  Model_types.cx -> Model_types.target -> (Tast.fn_def * Tast.block) option
(** The function's definition and body, for one with code. *)

val impl_args :
  Model_types.cx ->
  Model_types.target ->
  Types.ty list ->
  Types.ty list ->
  Env.fn_sig ->
  Types.ty list
(** The arguments of a generic impl that a call of one of its methods takes from
    its receiver's type, given the call's type arguments and its arguments'
    types. *)

val instance :
  Model_types.cx ->
  Model_types.target ->
  Types.ty list ->
  Types.ty list ->
  Model_types.fn_instance
(** The function at the type arguments of a call and the types of its arguments,
    which give its row parameters' rows, met and so declared. *)

val instantiated : Model_types.fn_instance -> Types.ty -> Types.ty
(** A type of the function's, at the instance's arguments. *)

val instantiated_row : Model_types.fn_instance -> Types.row -> Types.row

val body :
  Model_types.fn_instance ->
  Tast.fn_def ->
  Env.fn_sig ->
  Tast.block ->
  Tast.block
(** The function's body, of its definition and signature, at the instance's
    arguments. *)

val value : Model_types.cx -> Hir.item -> Types.ty list -> Model_json.t
(** A function declared at the top level as a value, at its type arguments. *)
