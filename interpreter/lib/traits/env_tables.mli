(** The tables of the environment, in which type checking looks up types,
    traits, impls and their members, and the diagnostics that building them
    reports.

    {!Env} exports the types and lookups of this module, and documents them
    (traits.impl-blocks and traits.method-resolution). *)

module Smap : Map.S with type key = string
module Imap : Map.S with type key = Hir.item
module Pmap : Map.S with type key = Hir.item * Hir.item
module Idmap : Map.S with type key = int
module Idset : Set.S with type elt = int

type bound = Types.bound = { trait : Hir.item; args : Types.ty list }
(** A bound: a trait with an argument for each of its parameters
    (traits.bound-arguments). *)

type bounds = (Hir.var * bound list) list

type fn_sig = {
  type_params : bounds;
  row_params : Hir.var list;
  params : (Types.mode * Types.ty) list;
  ret : Types.ty;
  projection : bool;
  row : Types.row;
  assumed : (Types.ty * bound) list;
}

type member_kind = Method of Types.mode | Function | Constant

type impl = {
  module_ : string;
  generics : bounds;
  trait_ : Hir.item option;
  trait_args : Types.ty list;
      (** The arguments it gives the trait's parameters, in terms of its
          generics (traits.trait-arguments). *)
  self_ty : Types.ty;
  loc : Ast.loc;
  members : member list;
  unknown : (string * Ast.loc) list;
}

and member = {
  name : string;
  pub : bool;
  kind : member_kind;
  signature : fn_sig;
  owner : Hir.item;
  impl_generics : bounds;
  self_ty : Types.ty;
}

type type_def =
  | Record of (string * Types.ty) list
  | Variants of (string * Types.ty list) list
  | Builtin

type type_info = { params : Hir.var list; def : type_def; pub : bool }

type trait_method = {
  method_name : string;
  method_sig : fn_sig;
  has_default : bool;
  member_kind : member_kind;
}

type trait_info = {
  self_param : Hir.var;
  params : Hir.var list;
  arity : int;
  methods : trait_method list;
  unknown_methods : string list;
      (** The methods that a syntax error leaves without a signature: every use
          of them has the error type, and an impl may hold them or not
          (errors.broken-parts). *)
}

type operation_sig = {
  op_params : (Types.mode * Types.ty) list;
  op_ret : Types.ty;
  op_row : Types.row;
}

(** An operation's signature, in terms of its effect's parameters
    (handlers.declaring-effect). *)

type effect_info = {
  eparams : Hir.var list;
  ops : (string * operation_sig) list;
}

type t = {
  types : type_info Imap.t;
  variants : (Hir.item * int * Types.ty list) Imap.t;
  functions : fn_sig Imap.t;
  constants : Types.ty Imap.t;
  traits : trait_info Imap.t;
  inherent : member list Imap.t;
  trait_impls : impl Pmap.t;
  module_traits : Hir.item list Smap.t;
  broken : (Hir.item option * string) list;
      (** The members of impls with errors, by type constructor where it is
          known. *)
  record_bounds : (string * Types.ty) list Idmap.t;
      (** The fields of the record bounds of type parameters, by id
          (records.bound-fields). *)
  packs : Idset.t;  (** The type parameters that are packs (variadics.packs). *)
  effects : effect_info Imap.t;  (** The effects (handlers.declaring-effect). *)
  foreign : unit Imap.t;
      (** The foreign functions, which C gives (c.foreign-functions). *)
}
(** The environment, which {!Env} keeps abstract. *)

(** {1 Lookups} *)

val type_info : t -> Hir.item -> type_info option
val variant : t -> Hir.item -> (Hir.item * int * Types.ty list) option
val function_sig : t -> Hir.item -> fn_sig option
val constant_type : t -> Hir.item -> Types.ty option
val trait_info : t -> Hir.item -> trait_info option
val effect_info : t -> Hir.item -> effect_info option
val is_foreign : t -> Hir.item -> bool
val inherent_members : t -> Hir.item -> member list
val trait_impl : t -> trait:Hir.item -> Hir.item -> impl option
val in_broken_impl : t -> Hir.item option -> string -> bool
val traits_of : t -> string -> Hir.item list
val trait_bounds : Hir.item list
val record_bound : t -> Hir.var -> (string * Types.ty) list option
val is_pack : t -> Hir.var -> bool

val record_fields : t -> Types.ty -> (string * Types.ty) list option
(** The traits of [std.prelude] that a type can implement structurally: [Eq],
    [Ord], [Hash] and [Show] (traits.structural-impls). *)

(** {1 Diagnostics} *)

type diagnostics = { mutable list : (bool * Diagnostic.t) list }
(** Each diagnostic, with whether it is in the standard library. *)

val report :
  diagnostics ->
  Hir.module_ ->
  Code.t ->
  Ast.loc ->
  ('a, unit, string, unit) format4 ->
  'a
(** [report d m code loc fmt] adds the diagnostic [code] at [loc] in module [m],
    with the message that [fmt] formats. *)
