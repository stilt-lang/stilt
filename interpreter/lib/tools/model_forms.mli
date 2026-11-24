(** The parts of the export of expressions that no expression's translation
    needs in turn: the operations on the world, the prelude's types,
    temporaries, patterns, and whether the prelude's structural impls of [Show]
    show a type. *)

val unit_e : Model_json.t
val var_e : string -> Model_json.t

val fn_result : Types.ty -> Types.ty
(** The result type of a function type. *)

val call_e :
  Model_types.cx ->
  Model_json.t ->
  Model_json.t list ->
  Types.ty ->
  Model_json.t
(** The call of a function value with its arguments, and the type of its result,
    which the calculus's call carries. *)

val map_item : Hir.item
val list_item : Hir.item
val option_item : Hir.item
val prelude_ty : string -> Types.ty
val is_map : Types.ty -> bool
val map_op : string -> Model_json.t list -> Model_json.t

val is_never : Types.ty -> bool
(** Whether a type is [Never], which no value has (declarations.never). *)

val ctor : Model_types.cx -> Hir.item -> Types.ty -> string * string
(** A constructor's type, as the calculus declares it for the type [t] of its
    values, and its name. *)

val eq_trait : Hir.item
val ord_trait : Hir.item
val show_trait : Hir.item
val ordering_item : Hir.item

val option_payload : Types.ty -> Types.ty
(** [T], for the type [Option<T>], and the type itself for any other. *)

val option :
  Model_types.cx -> Types.ty -> string -> Model_json.t list -> Model_json.t
(** A value of the type [t] of [Option<T>]: its constructor and payload. *)

val option_pattern :
  Model_types.cx -> Types.ty -> Model_json.t list -> Model_json.t
(** The pattern [Some(...)] of the type [t] of [Option<T>]. *)

val temp : string -> Ast.loc -> string
(** A name of a temporary of the export's, unique to the source position. *)

val structural_by : Model_types.cx -> string -> Types.ty -> bool
(** Whether the prelude's structural impls of the trait named give a type's impl
    of it, maps only for [Show]. *)

val structural : Model_types.cx -> Types.ty -> bool
(** Whether the prelude's structural impls of [Show] show a type. *)

val ctor_orders : Model_types.cx -> Types.ty -> (string * string list) list
(** The constructors of each variant type that a type holds, in declaration
    order, under the names the calculus declares those types by. *)

val on_world : string -> Model_json.t list -> Model_json.t list -> Model_json.t
(** The operation on the world of that name, with its fields, on its operands:
    ["write"], ["readLine"] or ["readAll"] (std.io). *)

val written : err:bool -> newline:bool -> Model_json.t -> Model_json.t
(** [s] appended to the output, or to standard error with [~err], then a newline
    with [~newline]: [print], [eprint], [io.write] and [io.ewrite]. *)

val pattern : Model_types.cx -> Tast.pattern -> Model_json.t
val binders : Tast.pattern -> Model_json.t list

val typed_binders : Tast.pattern -> (Hir.var * Types.ty) list
(** The variables a pattern binds, with their types. *)

val block_ty : Tast.block -> Types.ty
(** A block's type: its last expression's, or [()]. *)

val arm : Model_types.cx -> Tast.pattern -> Model_json.t -> Model_json.t
(** A [match]'s arm of a pattern and a body. *)

val eta :
  Tast.expr ->
  (Tast.arg list -> Types.row -> Tast.expr_desc) ->
  Tast.pattern list * Tast.expr
(** A function or a constructor as a value of a function type, as the parameters
    and body of the closure that calls it with them. *)

val constant : Model_types.cx -> Tast.expr -> Tast.expr
(** A constant's read, as the expression its value is. *)
