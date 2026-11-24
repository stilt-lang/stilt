(** The state of checking one body: what checking it has found so far, and where
    in it an expression is (types.inferred-per-body). *)

val by_value : Ast.mode
val by_inout : Ast.mode

(** The types that an operator applies to (numbers.no-implicit-conversions and
    numbers.comparisons). *)
type rule = Numeric | Integer | Negatable | Bool_or_integer

(** Where a value must have type [()] or [Never] (expressions.statements and
    expressions.if). An [if] without [else] carries its own type, which is [()]
    unless its block has another. *)
type unit_site = Statement | If_without_else of Types.ty

type literal = {
  lty : Types.ty;
  text : string;
  negative : bool;
  float : bool;
  lloc : Ast.loc;
}

(** A constant, by its name: a module's, or a type's ([Type.NAME]). *)
type constant =
  | Global of Hir.item
  | Assoc of Hir.item * string
  | Of_impl of Hir.item * Hir.item * string
      (** A trait impl's constant, by trait, type constructor and name
          (traits.trait-constants). *)

type fix = {
  fty : Types.ty;
  ftrait : Hir.item;
  fargs : Types.ty list;
  floc : Ast.loc;  (** Where an impl that gives others is reported. *)
  mutable fixed : bool;  (** Whether the arguments were made the impl's. *)
}
(** traits.trait-arguments and traits.bound-arguments: the arguments [fargs]
    that the impl of [ftrait] for [fty] must give the trait's parameters, which
    inference makes them once [fty] is known. *)

type need = {
  nty : Types.ty;
  nfields : (string * Types.ty) list;
  nloc : Ast.loc;  (** Where E0318 is reported. *)
  mutable met : bool;  (** Whether it was decided, once [nty] was known. *)
}
(** records.record-bounds: a type that must have [nfields], with their types,
    which a record bound names. *)

type spreading = {
  mutable named : (Hir.var * Types.ty) list;
      (** The pack tuples named so far, each with its pack. *)
  mutable mixed_at : Ast.loc option;
      (** Where the first tuple of another pack than the first is named. *)
  mutable closures : int;
      (** How many closure literals inside the spread the expression being
          checked is. *)
  mutable names_broken : bool;
      (** Whether it names a local whose type holds the error type. *)
}
(** variadics.spread-checks: what checking a spread expression has found so far.
*)

(** What a name that a pattern writes without a module names, once the pattern
    is checked (patterns.variants-by-type). *)
type named = Named_variant of Hir.item | Named_const | Named_error

type state = {
  env : Env.t;
  module_ : Hir.module_;
  traits : Hir.item list;  (** The traits visible to method calls. *)
  mutable bounds : Env.bounds;
  self : Types.ty option;  (** What [Self] means in a trait. *)
  locals : (int, Types.ty) Hashtbl.t;
  mutable errors : Diagnostic.t list;
  mutable broken : bool;
      (** Whether the body holds an error that resolution reported. *)
  mutable vars : Types.ty list;
  mutable unknown : int list;  (** Variables already reported as unknown. *)
  mutable obligations : (Types.ty * Hir.item * Ast.loc * Env.bounds) list;
      (** Each with the bounds where it arises: a bound test's branch adds to
          them (meta.bound-tests). *)
  mutable fixes : fix list;
  mutable operators : (Types.ty * rule * Ast.loc) list;
  mutable amounts : (Types.ty * Ast.loc) list;
      (** Shift amounts whose type was open where they were checked. *)
  mutable int_patterns : (Types.ty * Ast.loc) list;
  mutable literals : literal list;
  mutable units : (Types.ty * unit_site * Ast.loc) list;
  mutable specs : (Types.ty * string * Ast.loc) list;
  mutable constants : constant list;  (** The constants the body names. *)
  mutable catch_errors : Types.ty list;
      (** The error types of [catch]es whose operands may still raise. *)
  mutable passed : (Ast.loc * Types.row * Tast.label) list;
      (** What uses give the row variables their callees pair
          (effects.passing-to-paired-variables). *)
  bare : (Ast.loc, named) Hashtbl.t;
      (** What each name that a pattern writes without a module names, by the
          pattern's place, once checked. *)
  arrays : (Ast.loc, unit) Hashtbl.t;
      (** The list patterns that match arrays, by place, which, once they fit
          their sizes, can't fail when their elements can't
          (generics.array-patterns). *)
  mutable unknown_names : (string * Diagnostic.t) list;
      (** The E0211 of those names that name nothing, among [errors], each with
          its name, of which the body keeps one per name (errors.unknown-names).
      *)
  mutable needs : need list;
  mutable spreading : spreading option;
      (** Inside a spread expression, what it names (variadics.spread-checks).
      *)
  mutable splices : (Types.ty * Hir.place * Ast.loc) list;
      (** The type of each splice of a quote, where it stands, and its [$],
          which must fit there, decided at the end of the body (macros.splices).
      *)
  mutable unsafe_depth : int;
      (** How many [unsafe] blocks hold the expression being checked
          (c.unsafe-operations). *)
  mutable unsafe_blocks : Ast.loc list;
      (** The positions of the body's [unsafe] blocks, its closures' included,
          latest first (c.unsafe-and-foreign). *)
  mutable c_elements : (Types.ty * Ast.loc) list;
      (** The [T] of each call that reads, writes or lends C memory, with the
          call, which C must hold, decided at the end of the body
          (c.element-types and c.lending-buffer). *)
}
(** What checking one body has found so far. *)

type ctx = {
  st : state;
  ret : Types.ty;  (** The type that [return] returns. *)
  yields : Types.ty option;
      (** The type of the place that [yield] hands the caller, in a projection's
          body, and [None] anywhere else (projections.yield). *)
  effects : (Types.row * Ast.loc) list ref;  (** Latest first. *)
  known : (Hir.item * Types.ty list) list;
      (** The effects that the rows around the expression hold, those of the
          innermost [with] first, which give a performance its type arguments
          (handlers.performing-operation). *)
  resume : (Types.ty * Types.ty) option;
      (** In an operation's body of a handler that takes control, the
          operation's result type, which [resume] takes, and the handler's [R],
          which it gives (handlers.resuming). *)
  infer : ctx -> Types.ty option -> Hir.expr -> Tast.expr;
      (** [Check_exprs.infer], through which the checks of an expression's
          parts, in the modules before it, check their own parts. *)
}
(** Where in a body an expression is. *)

val error : state -> Code.t -> Ast.loc -> ('a, unit, string, unit) format4 -> 'a
(** [error st code loc fmt] records the error [code] at [loc], with the message
    that [fmt] formats. *)

val fresh : state -> ?kind:Types.kind -> Ast.loc -> Types.ty
(** A new type variable, of the expression at [loc]. *)

val show : Types.ty -> string
val is_never : Types.ty -> bool
val node : Tast.expr_desc -> Tast.ty -> Ast.loc -> Tast.expr
val error_node : Ast.loc -> Tast.expr

val literal :
  state -> text:string -> negative:bool -> float:bool -> Ast.loc -> Types.ty
(** The type of a numeric literal, whose range is checked at the end of the
    body, after it takes its default type (numbers.integer-literals,
    numbers.float-literals, numbers.literal-defaults and
    numbers.negative-literals). *)

val obligation : state -> Types.ty -> Hir.item -> Ast.loc -> unit
(** Requires a type to implement a trait, which is decided at the end of the
    body (traits.bounds). *)

val fix : state -> Types.ty -> Hir.item -> Types.ty list -> Ast.loc -> unit
(** [fix st ty trait args loc] requires the impl of [trait] for [ty] to give the
    trait's parameters [args] (traits.trait-arguments and
    traits.bound-arguments), which inference makes them once [ty] is known. One
    that gives others is E0318 at [loc]. *)

val improve : state -> unit
(** Makes the arguments of each fix whose type is now known those that its impl
    gives (traits.bound-arguments), and decides each need whose type is now
    known (records.record-bounds). *)

val require_fields :
  state -> Types.ty -> (string * Types.ty) list -> Ast.loc -> unit
(** [require_fields st ty fields loc] requires [ty] to be a record with each of
    [fields], of exactly its type, or else is E0318 at [loc]
    (records.bound-fields), decided once [ty] is known. *)

val prelude_trait : string -> Hir.item
