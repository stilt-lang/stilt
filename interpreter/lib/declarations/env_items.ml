(* The signatures of every module's items: its types and their variants,
   functions, constants and traits. *)

module T = Types
open Env_tables
open Env_signatures

let synthetic = Env_signatures.synthetic

let builtin_types =
  let plain = T.integer_types @ T.float_types @ [ "bool"; "str"; "Never" ] in
  List.map (fun name -> (name, [])) plain
  @ [ ("List", [ synthetic "T" ]); ("Map", [ synthetic "K"; synthetic "V" ]) ]

let decl_name (d : Hir.decl Hir.node) =
  match d.desc.kind with
  | Fn f -> f.name
  | Const c -> c.name
  | Type t -> t.name
  | Trait t -> t.name
  | Effect e -> e.name
  | Test _ -> invalid_arg "Env.decl_name"

let add_first key value map =
  if Imap.mem key map then map else Imap.add key value map

(* meta.std-meta and meta.shapes: [std.meta]'s [Shape] is a native variant type,
   whose cases patterns name. *)
let native_variants env shape (t : Hir.type_decl) =
  let cases = Meta.cases (T.Param (List.hd t.params)) in
  let variants, _ =
    List.fold_left
      (fun (variants, i) (name, payload) ->
        (add_first (Meta.item name) (shape, i, [ payload ]) variants, i + 1))
      (env.variants, 0) cases
  in
  ( Variants (List.map (fun (name, payload) -> (name, [ payload ])) cases),
    variants )

let declare_type env item pub (t : Hir.type_decl) =
  let payload_of (v : Hir.variant_decl) = List.map of_hir v.payload in
  let native = item t.name = Meta.shape && t.def = Native in
  let def : type_def =
    match t.def with
    | _ when native -> fst (native_variants env Meta.shape t)
    | Record fields ->
        Record
          (List.map
             (fun ({ field; ty } : Hir.field_decl) -> (field.desc, of_hir ty))
             fields)
    | Variants vs ->
        Variants
          (List.map
             (fun (v : Hir.variant_decl) -> (v.name.desc, payload_of v))
             vs)
    | Native -> Builtin
  in
  let variants =
    match t.def with
    | _ when native -> snd (native_variants env Meta.shape t)
    | Record _ | Native -> env.variants
    | Variants vs ->
        List.fold_left
          (fun (variants, i) (v : Hir.variant_decl) ->
            ( add_first (item v.name) (item t.name, i, payload_of v) variants,
              i + 1 ))
          (env.variants, 0) vs
        |> fst
  in
  {
    env with
    types = Imap.add (item t.name) { params = t.params; def; pub } env.types;
    variants;
  }

(* A trait's member: a method, a function without [self] or a constant
   (traits.declaring-trait; traits.functions-without-self and traits.trait-constants). *)
let trait_member self (member : Hir.decl Hir.node) =
  match member.desc.kind with
  | _ when member.desc.unknown -> None
  | Fn f ->
      Some
        {
          method_name = f.name.desc;
          method_sig = signature ~self ~self_ty:self ~outer:[] f;
          has_default = Option.is_some f.body;
          member_kind =
            (match f.params with
            | Self_param (mode, _, _) :: _ -> Method mode
            | _ -> Function);
        }
  | Const c ->
      Some
        {
          method_name = c.name.desc;
          method_sig =
            {
              type_params = [];
              row_params = [];
              assumed = [];
              params = [];
              ret = of_hir ~self c.ty;
              projection = false;
              row = T.empty_row;
            };
          has_default = Option.is_some c.value;
          member_kind = Constant;
        }
  | Type _ | Trait _ | Test _ | Effect _ -> None

(* handlers.declaring-effect: an effect's operations, their signatures in terms of its
   type parameters. *)
let declare_effect env item (e : Hir.effect_decl) =
  let op (o : Hir.operation) =
    ( o.op.desc,
      {
        op_params = List.map (fun (mode, _, t) -> (mode, of_hir t)) o.params;
        op_ret = Option.fold ~none:T.unit ~some:of_hir o.ret;
        op_row = of_hir_row o.row;
      } )
  in
  {
    env with
    effects =
      add_first item { eparams = e.params; ops = List.map op e.ops } env.effects;
  }

let declare_trait env (m : Hir.module_) trait (t : Hir.trait_decl) =
  let self_param = synthetic "Self" in
  let self = T.Param self_param in
  let methods = List.filter_map (trait_member self) t.members in
  let unknown_methods =
    List.filter_map
      (fun (member : Hir.decl Hir.node) ->
        if member.desc.unknown then Some (decl_name member).desc else None)
      t.members
  in
  let info =
    { self_param; params = t.params; arity = t.arity; methods; unknown_methods }
  in
  {
    env with
    traits = Imap.add trait info env.traits;
    module_traits =
      Smap.update m.name
        (fun ts -> Some (Option.value ts ~default:[] @ [ trait ]))
        env.module_traits;
  }

(* Every type parameter that the program declares, in its functions, traits
   and impls. *)
let program_params (program : Hir.program) =
  let of_fn (f : Hir.fn_decl) =
    List.filter_map
      (function Hir.Type_param p -> Some p | Row_param _ -> None)
      f.generics
  in
  let of_decl (d : Hir.decl Hir.node) =
    match d.desc.kind with
    | Fn f -> of_fn f
    | Trait t ->
        List.concat_map
          (fun (m : Hir.decl Hir.node) ->
            match m.desc.kind with Fn f -> of_fn f | _ -> [])
          t.members
    | Type _ | Const _ | Test _ | Effect _ -> []
  in
  List.concat_map
    (fun (m : Hir.module_) ->
      List.concat_map of_decl m.decls
      @ List.concat_map
          (fun (i : Hir.impl_decl Hir.node) ->
            i.desc.generics @ List.concat_map of_decl i.desc.members)
          m.impls)
    program

(* records.record-bounds, and variadics.packs: the record bounds and the packs of
   type parameters. *)
let declare_params env (params : Hir.type_param list) =
  List.fold_left
    (fun env (p : Hir.type_param) ->
      let env =
        if p.pack then { env with packs = Idset.add p.var.id env.packs }
        else env
      in
      match p.fields with
      | [] -> env
      | fields ->
          let fields =
            List.map
              (fun (f : Hir.field_decl) -> (f.field.desc, of_hir f.ty))
              fields
          in
          {
            env with
            record_bounds = Idmap.add p.var.id fields env.record_bounds;
          })
    env params

(* The items of every module. Of two items with the same name, the first is
   the one names refer to, and resolution reports the other. *)
let declare_items (program : Hir.program) =
  let builtins =
    List.fold_left
      (fun types (name, params) ->
        Imap.add (T.prelude_item name)
          { params; def = Builtin; pub = true }
          types)
      Imap.empty builtin_types
  in
  let empty =
    {
      types = builtins;
      variants = Imap.empty;
      functions = Imap.empty;
      constants = Imap.empty;
      traits = Imap.empty;
      inherent = Imap.empty;
      trait_impls = Pmap.empty;
      module_traits = Smap.empty;
      broken = [];
      record_bounds = Idmap.empty;
      packs = Idset.empty;
      effects = Imap.empty;
      foreign = Imap.empty;
    }
  in
  let empty = declare_params empty (program_params program) in
  List.fold_left
    (fun env (m : Hir.module_) ->
      let item (n : Hir.name) = { Hir.home = m.name; name = n.desc } in
      List.fold_left
        (fun env (decl : Hir.decl Hir.node) ->
          match decl.desc.kind with
          | Fn f ->
              let s = signature ~outer:[] f in
              let foreign =
                if decl.desc.foreign then Imap.add (item f.name) () env.foreign
                else env.foreign
              in
              {
                env with
                functions = add_first (item f.name) s env.functions;
                foreign;
              }
          | Const c ->
              {
                env with
                constants = add_first (item c.name) (of_hir c.ty) env.constants;
              }
          | Type t when Imap.mem (item t.name) env.types -> env
          | Type t -> declare_type env item decl.desc.pub t
          | Trait t when Imap.mem (item t.name) env.traits -> env
          | Trait t -> declare_trait env m (item t.name) t
          | Effect e -> declare_effect env (item e.name) e
          | Test _ -> env)
        env m.decls)
    empty program
