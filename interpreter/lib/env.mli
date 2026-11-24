(** The signatures of a program's items, and the tables in which type checking
    looks up types, traits, impls and their members.

    Building the environment also checks every rule about declarations that
    needs no function body: where impls may be written and what they must hold
    (traits.impl-blocks, traits.implementing-trait and traits.coherence),
    records that contain themselves (declarations.recursive-types), and the
    signature of [main] (program.main). *)

type bound = Types.bound = { trait : Hir.item; args : Types.ty list }
(** A bound: a trait with an argument for each of its parameters
    (traits.bound-arguments). *)

type bounds = (Hir.var * bound list) list
(** Type parameters with the traits they are bounded by. A bound with an error
    is left out, since the error type satisfies every bound (errors.error-type).
*)

type fn_sig = {
  type_params : bounds;
  row_params : Hir.var list;
  params : (Types.mode * Types.ty) list;
      (** The parameters' types, the receiver's first for a method. *)
  ret : Types.ty;
  projection : bool;
      (** Whether its result is written [inout T]: a call of it is a place
          (projections.declaring-projection and projections.call-is-place). *)
  row : Types.row;
  assumed : (Types.ty * bound) list;
      (** The bounds of its [where] clause on its impl block's member types,
          which its body assumes and its calls meet (traits.where). *)
}

type member_kind =
  | Method of Types.mode  (** A function that takes [self], in this mode. *)
  | Function  (** An associated function. *)
  | Constant  (** An associated constant, whose type is the [ret]. *)

type impl = {
  module_ : string;
  generics : bounds;
  trait_ : Hir.item option;  (** [None] for an inherent impl. *)
  trait_args : Types.ty list;
      (** The arguments it gives the trait's parameters, in terms of its
          generics (traits.trait-arguments). *)
  self_ty : Types.ty;
  loc : Ast.loc;  (** The impl's [impl] keyword. *)
  members : member list;
  unknown : (string * Ast.loc) list;
      (** The members that a syntax error leaves without a signature, each with
          the place of its name (errors.broken-parts). *)
}

and member = {
  name : string;
  pub : bool;  (** Whether other modules can use it (program.visibility). *)
  kind : member_kind;
  signature : fn_sig;
      (** The impl's generics come first among its type parameters. *)
  owner : Hir.item;  (** The type constructor whose member it is. *)
  impl_generics : bounds;
  self_ty : Types.ty;  (** The impl's type, in terms of [impl_generics]. *)
}

type type_def =
  | Record of (string * Types.ty) list
  | Variants of (string * Types.ty list) list
  | Builtin
      (** A type without a written representation: a built-in type of
          [std.prelude], such as [i64] or [List], or a native type of the
          standard library, such as [std.view.View] (views.std-view). *)

type type_info = { params : Hir.var list; def : type_def; pub : bool }

type trait_method = {
  method_name : string;
  method_sig : fn_sig;
      (** [Self] is the trait's [self_param], and its parameters are the trait's
          [params]. A constant's type is the [ret]. *)
  has_default : bool;
  member_kind : member_kind;
      (** A method, a function without [self] or a constant
          (traits.functions-without-self and traits.trait-constants). *)
}

type trait_info = {
  self_param : Hir.var;
  params : Hir.var list;  (** Its trait parameters (traits.trait-parameters). *)
  arity : int;
      (** For a constructor trait, the number of arguments its [Self] takes, and
          0 for a trait over types (traits.constructor-traits). *)
  methods : trait_method list;
      (** Its functions and constants, which its impls hold. *)
  unknown_methods : string list;
      (** The methods that a syntax error leaves without a signature: every use
          of them has the error type, and an impl may hold them or not
          (errors.broken-parts). *)
}

type operation_sig = Env_tables.operation_sig = {
  op_params : (Types.mode * Types.ty) list;
  op_ret : Types.ty;
  op_row : Types.row;
}
(** An operation's signature, in terms of its effect's parameters
    (handlers.declaring-effect). *)

type effect_info = Env_tables.effect_info = {
  eparams : Hir.var list;
  ops : (string * operation_sig) list;
}
(** An effect: its type parameters and its operations, by name. *)

type t

val build : Hir.program -> t * Diagnostic.t list
(** The environment of a program, and the errors in its declarations. An impl
    with an error adds no members, but the names it declares are known (see
    {!in_broken_impl}).

    @raise Failure if the standard library has errors, which is a bug in it. *)

(** {1 Lookups} *)

val type_info : t -> Hir.item -> type_info option

val variant : t -> Hir.item -> (Hir.item * int * Types.ty list) option
(** A variant's type, its position among the type's variants, and its payload's
    types, in terms of the type's [params]. *)

val function_sig : t -> Hir.item -> fn_sig option
val constant_type : t -> Hir.item -> Types.ty option
val trait_info : t -> Hir.item -> trait_info option
val effect_info : t -> Hir.item -> effect_info option

val is_foreign : t -> Hir.item -> bool
(** Whether a function is foreign, which C gives (c.foreign-functions). *)

val inherent_members : t -> Hir.item -> member list
(** The members of every inherent impl of a type constructor. *)

val trait_impl : t -> trait:Hir.item -> Hir.item -> impl option
(** [trait_impl env ~trait owner] is the impl of [trait] that the program writes
    for the type constructor [owner], if it writes one. *)

val in_broken_impl : t -> Hir.item option -> string -> bool
(** [in_broken_impl env owner name] tells whether an impl with an error declares
    a member [name], for the type constructor [owner] or for one that its error
    hides. Uses of such a member have the error type
    (errors.declarations-with-errors). *)

val traits_of : t -> string -> Hir.item list
(** The traits that a module declares. *)

val record_bound : t -> Hir.var -> (string * Types.ty) list option
(** The fields that a type parameter's record bounds name, if it has one
    (records.record-bounds). *)

val record_fields : t -> Types.ty -> (string * Types.ty) list option
(** The fields of a type known to have them: a declared record, with its type
    arguments, an anonymous record, or a type parameter with a record bound, the
    fields its bound names (records.bound-fields and records.update-fields). *)

val is_pack : t -> Hir.var -> bool
(** Whether a type parameter is a pack (variadics.packs). *)

val synthetic : ?loc:Ast.loc -> string -> Hir.var
(** A new variable that no declaration has, such as the [Self] parameter of a
    trait or the parameter of a key path's closure. *)

(** {1 Types} *)

val of_hir : ?self:Types.ty -> Hir.ty -> Types.ty
(** The type that a written type stands for. [self] is what [Self] means in a
    trait, a type parameter. *)

val bounds_of : ?self:Types.ty -> Hir.type_param list -> bounds
(** The bounds of type parameters, with their arguments. *)

val signature :
  ?self:Types.ty -> ?self_ty:Types.ty -> outer:bounds -> Hir.fn_decl -> fn_sig
(** The signature of a function. [self] is what [Self] means, [self_ty] the
    receiver's type, and [outer] the generics of the impl that holds the
    function, which come first. Each non-escaping parameter's row, and the
    function's own row, hold the parameter's implicit row variable
    (effects.non-escaping-parameters). *)

val passing : fn_sig -> bool list
(** For each parameter of a signature, the receiver's first, whether it is
    non-escaping (effects.non-escaping-parameters). *)

(** Whether a type implements a trait. *)
type answer =
  | Yes
  | No
  | Unknown  (** It depends on a type variable that isn't solved yet. *)

val implements : t -> bounds -> Types.ty -> Hir.item -> answer
(** [implements env bounds ty trait] tells whether [ty] implements [trait],
    through an impl the program writes or a structural impl
    (traits.structural-impls), where the type parameters in [ty] have [bounds].
    The error type implements every trait. *)

val impl_subst :
  t -> bounds -> impl -> Types.ty list -> (Hir.var * Types.ty) list
(** [impl_subst env bounds impl args] applies [impl] to [args], the type
    arguments of its type constructor: it gives each of the impl's generics that
    its type names its argument, and each that a member type implies the
    argument that the impl of its bound gives (traits.trait-arguments and
    traits.member-types). *)

val trait_args : t -> bounds -> Types.ty -> Hir.item -> Types.ty list option
(** [trait_args env bounds ty trait] is the list of arguments that the impl of
    [trait] for [ty], or the bound of the type parameter [ty], gives the trait's
    parameters (traits.trait-arguments and traits.bound-arguments), if there is
    one. *)

val has_impl : t -> Types.ty -> Hir.item -> bool
(** [has_impl env ty trait] tells whether the head constructor of [ty], a named
    type or a tuple, has an impl of [trait], written or structural, whatever the
    bounds of that impl ask of its arguments (traits.method-resolution). *)
