(* The tables of the environment, in which type checking looks up types,
   traits, impls and their members, and the diagnostics that building them
   reports. *)

module T = Types
module Smap = Map.Make (String)

(* Items in the order of [compare] on their records, by home and then by name,
   without its generic walk over them, which type checking spends much of its
   time in. *)
let compare_items (a : Hir.item) (b : Hir.item) =
  match String.compare a.home b.home with
  | 0 -> String.compare a.name b.name
  | c -> c

module Imap = Map.Make (struct
  type t = Hir.item

  let compare = compare_items
end)

module Idmap = Map.Make (Int)
module Idset = Set.Make (Int)

module Pmap = Map.Make (struct
  type t = Hir.item * Hir.item

  let compare (a, b) (c, d) =
    match compare_items a c with 0 -> compare_items b d | n -> n
end)

type bound = T.bound = { trait : Hir.item; args : T.ty list }
(** A bound: a trait with an argument for each of its parameters
    (traits.bound-arguments). *)

type bounds = (Hir.var * bound list) list

type fn_sig = {
  type_params : bounds;
  row_params : Hir.var list;
  params : (T.mode * T.ty) list;
  ret : T.ty;
  projection : bool;
  row : T.row;
  assumed : (T.ty * bound) list;
}

type member_kind = Method of T.mode | Function | Constant

type impl = {
  module_ : string;
  generics : bounds;
  trait_ : Hir.item option;
  trait_args : T.ty list;
      (** The arguments it gives the trait's parameters, in terms of its
          generics (traits.trait-arguments). *)
  self_ty : T.ty;
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
  self_ty : T.ty;
}

type type_def =
  | Record of (string * T.ty) list
  | Variants of (string * T.ty list) list
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
}

type operation_sig = {
  op_params : (Types.mode * Types.ty) list;
  op_ret : Types.ty;
  op_row : Types.row;
}

type effect_info = {
  eparams : Hir.var list;
  ops : (string * operation_sig) list;
}

type t = {
  types : type_info Imap.t;
  variants : (Hir.item * int * T.ty list) Imap.t;
  functions : fn_sig Imap.t;
  constants : T.ty Imap.t;
  traits : trait_info Imap.t;
  inherent : member list Imap.t;
  trait_impls : impl Pmap.t;
  module_traits : Hir.item list Smap.t;
  broken : (Hir.item option * string) list;
  record_bounds : (string * T.ty) list Idmap.t;
      (** The fields of the record bounds of type parameters, by id
          (records.bound-fields). *)
  packs : Idset.t;  (** The type parameters that are packs (variadics.packs). *)
  effects : effect_info Imap.t;  (** The effects (handlers.declaring-effect). *)
  foreign : unit Imap.t;
      (** The foreign functions, which C gives (c.foreign-functions). *)
}

let type_info env item = Imap.find_opt item env.types
let variant env item = Imap.find_opt item env.variants
let function_sig env item = Imap.find_opt item env.functions
let constant_type env item = Imap.find_opt item env.constants
let trait_info env item = Imap.find_opt item env.traits
let effect_info env item = Imap.find_opt item env.effects
let is_foreign env item = Imap.mem item env.foreign

let inherent_members env item =
  Option.value (Imap.find_opt item env.inherent) ~default:[]

let trait_impl env ~trait item = Pmap.find_opt (trait, item) env.trait_impls

let in_broken_impl env owner name =
  List.exists (fun (o, n) -> n = name && (o = None || o = owner)) env.broken

let traits_of env module_ =
  Option.value (Smap.find_opt module_ env.module_traits) ~default:[]

let trait_bounds = List.map T.prelude_item [ "Eq"; "Ord"; "Hash"; "Show" ]
let record_bound env (v : Hir.var) = Idmap.find_opt v.id env.record_bounds
let is_pack env (v : Hir.var) = Idset.mem v.id env.packs

(* records.bound-fields and records.update-fields: the fields of a type that is known to have them:
   a declared record's, with its type arguments, an anonymous record's, and
   those that a type parameter's record bound names. *)
let record_fields env ty =
  match T.resolve ty with
  | T.Con (item, args) -> (
      match Imap.find_opt item env.types with
      | Some { def = Record fields; params; _ }
        when List.length params = List.length args ->
          let sub = List.combine params args in
          Some (List.map (fun (name, t) -> (name, T.subst sub [] t)) fields)
      | _ -> None)
  | Record fields -> Some fields
  | Param v -> record_bound env v
  | _ -> None

(* Diagnostics *)

type diagnostics = { mutable list : (bool * Diagnostic.t) list }

let report d (m : Hir.module_) code (loc : Ast.loc) fmt =
  Printf.ksprintf
    (fun message ->
      let diagnostic =
        {
          Diagnostic.code;
          file = m.file;
          line = loc.line;
          col = loc.col;
          message;
        }
      in
      d.list <- (m.std, diagnostic) :: d.list)
    fmt
