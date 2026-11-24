(** The types that the type checker works with.

    A type may hold unification variables, which inference creates inside one
    body and solves before the body is done (types.inferred-per-body; principle
    2 of the design sketch). Everything else is fixed by signatures. *)

type mode = Ast.mode

(** What an unsolved type variable may become. *)
type kind =
  | Any
  | Int_literal
      (** The type of an integer literal: any numeric type
          (numbers.integer-literals). *)
  | Float_literal
      (** The type of a float literal: a float type (numbers.float-literals). *)

type ty =
  | Con of Hir.item * ty list
      (** A named type with its arguments, the built-in types included. *)
  | Param of Hir.var
      (** A type parameter, which is rigid where it is declared. [Self] in a
          trait is a parameter too. *)
  | Tuple of ty list
  | Record of (string * ty) list
      (** An anonymous record type, with its fields in the alphabetical order of
          their names (records.anonymous-types and records.field-order).
          {!record} makes one. *)
  | Spread of ty * ty
      (** [..T], an element of a tuple or a parameter of a function type, and
          nothing else: its pack, a type parameter or a variable that stands for
          the pack's elements as a tuple, and [T], which names it
          (variadics.type-spreads). *)
  | Fn of (mode * ty) list * ty * row
  | App of ty * ty list
      (** A constructor parameter, or a variable that stands for a constructor,
          applied to arguments, as [F<i64>] (traits.constructor-parameters).
          Once its head is solved, {!resolve} gives the type it makes. A
          constructor stands alone only as such a head, or as what a constructor
          parameter or a constructor trait's [Self] is: a [Con] with no
          arguments. *)
  | Forall of forall
      (** A polymorphic function type (polymorphism.function-types), which only
          a parameter, a field or a payload has. *)
  | Handler of handler
      (** A handler's type (handlers.handler-types), which only a handler
          literal and the handlers of [std.task] have. *)
  | Var of var
  | Value of string
      (** A value argument: a value of a value parameter's type, in decimal, or
          [true] or [false] (generics.value-arguments). Two are one type exactly
          when their values are (generics.equal-types). A value parameter given
          as one is a [Param]. *)
  | Error  (** The error type of errors.error-type. *)

and handler = {
  eff : Hir.item;
  hargs : ty list;  (** The effect's type arguments. *)
  answer : ty option;  (** The [R] of a handler that takes control. *)
  hrow : row;  (** What its operations perform beyond their own rows. *)
}

and forall = {
  generics : (Hir.var * bound list) list;
      (** Its type parameters with their bounds, which hold in its body. *)
  body : ty;  (** A function type. *)
}

and bound = { trait : Hir.item; args : ty list }
(** A bound: a trait with an argument for each of its parameters
    (traits.bound-arguments). *)

and var
(** A unification variable. *)

and row = {
  io : bool;
  raise : ty option;
  effects : (Hir.item * ty list) list;
      (** Its effects, each once, with their type arguments
          (handlers.effects-in-rows), [async] among them (tasks.async). *)
  tail : tail;
}
(** An effect row (effects.rows). *)

and tail =
  | Closed
  | Row_params of row_param list
      (** Row variables of a signature, at least one, each once. A row that is
          written holds one, and a function's own row, or a row that a body
          forms, may hold several (effects.row-variables). *)
  | Row_var of row_var  (** A row being inferred, such as that of a closure. *)

and row_param = {
  var : Hir.var;
  implicit : bool;
      (** Whether it is the implicit row variable of a non-escaping parameter,
          named after the parameter (effects.non-escaping-parameters). *)
}

and row_var
(** An open row: the least row that holds every effect added to it, until it is
    closed by being unified with a row of a signature. *)

(** {1 Built-in types} *)

val prelude_item : string -> Hir.item
val never : ty
val unit : ty
val bool : ty
val str : ty
val i64 : ty
val f64 : ty
val list : ty -> ty
val map : ty -> ty -> ty
val option : ty -> ty
val integer_types : string list
val float_types : string list

val numeric_name : ty -> string option
(** The name of a numeric type, such as [Some "u8"]. *)

val record : (string * ty) list -> ty
(** The anonymous record type of these fields, in any order. *)

val async_effect : Hir.item
(** The effect [async] (tasks.async), which no module declares. *)

val anonymous : Hir.item
(** The item that the values and literals of anonymous records name, which no
    module declares (records.no-home). *)

(** {1 Packs (variadics.packs)} *)

val same_pack : ty -> ty -> bool
(** Whether two types are the same pack: one type parameter, or one variable. *)

val replace : ty -> ty -> ty -> ty
(** [replace pack by t] is [t] with [by] in place of [pack], a type parameter or
    a variable that stands for a pack. *)

val element : ty -> ty -> ty -> ty
(** [element pack body e] is the element of the spread [..body] of [pack] at the
    pack's element [e]: [body] with [e] in place of the pack, or a spread of
    [e]'s pack where [e] is a spread. *)

val expand : ty list -> ty list
(** Elements, of a tuple or of a function type's parameters, with each spread
    whose pack is known as one element for each of the pack's
    (variadics.type-spreads). *)

(** {1 Variables} *)

val fresh : ?kind:kind -> Ast.loc -> ty
(** A new unification variable, created by the expression at the location. *)

val fresh_row : ?least:bool -> unit -> row
(** A row that is only an open row with nothing in it yet. A [least] row stands
    for the union of the rows of some function values, such as the elements of a
    list literal, or for the effects of a closure's body
    (effects.function-value-unions). Only those can add effects to it: unifying
    it with another row never does. *)

val empty_row : row

val resolve : ty -> ty
(** The type with its outermost solved variables replaced by their solutions,
    and an [App] whose head is a constructor replaced by the type it makes. A
    head that is a type but no constructor makes the error type. A tuple's or a
    function type's spreads whose packs are known are {!expand}ed. *)

val apply : ty -> ty list -> ty
(** [apply head args] is [head] applied to [args], resolved. *)

val zonk : ty -> ty
(** The type with every solved variable replaced, at every depth. *)

type var_info = {
  id : int;
  kind : kind;
  origin : Ast.loc;
  tainted : bool;
      (** Whether the variable has met the error type, so that what it stands
          for may be unknown because of another error (errors.error-type). *)
}

val origin : ty -> Ast.loc option
(** Where the variable [t] itself was made, whatever variable it was later made
    one with, or [None] if [t] isn't a variable. *)

val unsolved : ty -> var_info option
(** The unsolved variable that the type is, if it is one. *)

val solve : ty -> ty -> unit
(** [solve v t] solves the unsolved variable [v] with [t]. The variables of [t]
    are tainted if [v] was. *)

val rigid : Hir.var -> ty
(** A rigid type for the new type parameter [v] (polymorphism.rigid-types): no
    variable made before it may come to stand for a type that holds it. *)

val is_rigid : Hir.var -> bool

val would_escape : ty -> ty -> bool
(** [would_escape v t] tells whether solving the unsolved variable [v] with [t]
    would let a rigid type that [t] holds reach a variable older than it. *)

val occurs : ty -> ty -> bool
(** [occurs v t] tells whether the unsolved variable [v] occurs in [t]. *)

val taint : ty -> unit
(** Taints every unsolved variable in the type, as meeting the error type does.
*)

val mentions_error : ty -> bool
(** Whether the error type occurs in the type. *)

(** {1 Rows} *)

(** What an open row is so far. *)
type row_state =
  | Open of row
      (** The effects added so far. Their tail is [Closed] or row parameters. *)
  | Link of row
      (** The open row is this row. Its upper bounds have moved to it. *)

val row_state : row_var -> row_state
val set_row_state : row_var -> row_state -> unit

val row_contents : row -> row
(** The effects the row holds now: links followed, and each open row replaced by
    the effects added to it so far. Its tail is [Closed] or row parameters. An
    open row may hold more later, which reach its upper bounds. *)

val is_open : row -> bool
(** Whether the row ends in an open row, which may still grow. *)

val least : row_var -> bool

(** What a row loses on its way to another: nothing, a raise of a type, which a
    [try … catch] handles, or an effect, which a [with] handles (handlers.with).
*)
type handled = Nothing | Raise_of of ty | Effect_of of Hir.item * ty list

val uppers : row_var -> (row * handled) list
(** The rows an open row must fit in, each with what it loses on the way. *)

val add_upper : row_var -> row * handled -> unit

val row_occurs : row_var -> ty -> bool
(** [row_occurs rv t] tells whether the open row [rv] occurs in [t], through the
    rows of its function types. *)

val row_mentions : row_var -> row -> bool
(** [row_mentions rv r] tells whether the open row [rv] occurs in [r]: as its
    tail, or in its raise type or its effects' arguments. *)

val find_effect : Hir.item -> row -> ty list option
(** The type arguments of the effect that a row holds, if it holds it. *)

val without_effect : Hir.item -> row -> row
(** The row without the effect. *)

val map_effects :
  (ty -> ty) -> (Hir.item * ty list) list -> (Hir.item * ty list) list
(** The effects of a row with each argument mapped. *)

val merge_labels : row -> row -> row
(** [merge_labels r extra] adds the labels of [extra] to [r]. Where both raise,
    the type of [r] is kept. *)

(** {1 Row parameters} *)

val params : row -> row_param list
(** The row parameters that the row holds now. *)

val has_param : row_param list -> row_param -> bool
val union_params : row_param list -> row_param list -> row_param list

val params_tail : row_param list -> tail
(** [Row_params], or [Closed] for none. *)

val type_params : ty -> Hir.var list
(** The type parameters that occur in the type, at any depth, in order. *)
