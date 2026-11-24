(* Which bodies of a program have an error, as program.bodies-with-errors defines it for
   [run]: those in whose declaration an error lies, and those that meet the
   error type. [run] replaces each with a [check-error] panic. *)

module T = Types
module A = Tast
open Syntax_parts

module Names = Set.Make (struct
  type t = string * Ast.loc

  let compare = compare
end)

(* {1 Errors that lie in a body} *)

let pos (d : Diagnostic.t) = (d.line, d.col)
let at (l : Ast.loc) = (l.line, l.col)
let before l d = at l < pos d
let within (e : extent) d = at e.first <= pos d && pos d <= at e.last

let body (e : extent) =
  match e.kind with Fn | Const | Test -> [ e.name ] | _ -> []

(* The names of the bodies in whose declaration [d] lies: the function,
   constant or test whose extent holds it, a member of a block, and every
   member of an impl whose header holds it after its [impl] keyword. *)
let lying extents (d : Diagnostic.t) =
  match List.find_opt (fun e -> within e d) extents with
  | None -> []
  | Some e -> (
      match (e.kind, List.find_opt (fun m -> within m d) e.members) with
      | (Fn | Const | Test | Macro), _ -> [ e.name ]
      | (Impl | Trait), Some m -> body m
      | Impl, None -> (
          match e.block with
          | Some b when before e.name d && pos d <= at b ->
              List.concat_map body e.members
          | _ -> [])
      | (Type | Trait | Syntax | Effect | Other), _ -> [])

(* {1 Signatures with errors} *)

let rec ty_error (t : Hir.ty) =
  match t.desc with
  | Ty_error -> true
  | Ty_con (_, ts) | Ty_tuple ts | Ty_app (_, ts) | Ty_self_app ts ->
      List.exists ty_error ts
  | Ty_record fields ->
      List.exists (fun (f : Hir.field_decl) -> ty_error f.ty) fields
  | Ty_spread (_, t) -> ty_error t
  | Ty_fn (_, ps, ret, row) ->
      List.exists (fun (_, t) -> ty_error t) ps
      || Option.fold ~none:false ~some:ty_error ret
      || Option.fold ~none:false ~some:ty_error row.raise
  | Ty_handler (e, answer, _) ->
      List.exists ty_error (e.args @ Option.to_list answer)
  | Ty_param _ | Ty_self | Ty_value _ -> false

let bound_error (p : Hir.type_param) =
  List.exists
    (fun (b : Hir.bound) ->
      b.trait = Hir.Trait_error || List.exists ty_error b.args)
    p.bounds
  || List.exists (fun (f : Hir.field_decl) -> ty_error f.ty) p.fields

let fn_error (f : Hir.fn_decl) =
  List.exists
    (function Hir.Type_param p -> bound_error p | Row_param _ -> false)
    f.generics
  || List.exists
       (function
         | Hir.Param (_, _, t, _) | Self_param (_, _, Some t) -> ty_error t
         | Self_param (_, _, None) -> false)
       f.params
  || Option.fold ~none:false ~some:ty_error f.ret
  || Option.fold ~none:false ~some:ty_error f.row.raise

let header_error (i : Hir.impl_decl) =
  ty_error i.self_ty
  || List.exists bound_error i.generics
  ||
  match i.trait_ with
  | Some b -> b.trait = Trait_error || List.exists ty_error b.args
  | None -> false

let decl_name (d : Hir.decl Hir.node) =
  match d.desc.kind with
  | Fn f -> Some f.name.loc
  | Const c -> Some c.name.loc
  | Type _ | Trait _ | Test _ | Effect _ -> None

(* The names of the declarations whose signature, or whose impl's header,
   holds a name with an error: one that has the error type. *)
let signature_errors (m : Hir.module_) =
  let own (d : Hir.decl Hir.node) =
    match d.desc.kind with
    | Fn f when fn_error f -> [ f.name.loc ]
    | Const c when ty_error c.ty -> [ c.name.loc ]
    | Trait t ->
        List.filter_map
          (fun (d : Hir.decl Hir.node) ->
            match d.desc.kind with
            | Fn f when fn_error f -> Some f.name.loc
            | Const c when ty_error c.ty -> Some c.name.loc
            | _ -> None)
          t.members
    | Fn _ | Const _ | Type _ | Test _ | Effect _ -> []
  in
  let impl (i : Hir.impl_decl Hir.node) =
    if header_error i.desc then List.filter_map decl_name i.desc.members
    else List.concat_map own i.desc.members
  in
  List.concat_map own m.decls @ List.concat_map impl m.impls

(* {1 Meeting the error type} *)

let rec holds (t : T.ty) =
  match T.resolve t with
  | Error -> true
  | Con (_, ts) | Tuple ts -> List.exists holds ts
  | Record fields -> List.exists (fun (_, t) -> holds t) fields
  | App (h, ts) -> List.exists holds (h :: ts)
  | Spread (p, t) -> holds p || holds t
  | Fn (ps, ret, row) ->
      List.exists (fun (_, t) -> holds t) ps || holds ret || row_holds row
  | Handler h ->
      List.exists holds (h.hargs @ Option.to_list h.answer) || row_holds h.hrow
  | Forall p -> holds p.body
  | Param _ | Var _ | Value _ -> false

and row_holds row =
  let r = T.row_contents row in
  List.exists holds (Option.to_list r.raise @ List.concat_map snd r.effects)

let sig_holds (s : Env.fn_sig) =
  List.exists (fun (_, t) -> holds t) s.params || holds s.ret || row_holds s.row

let callee_holds env : A.callee -> bool = function
  | Function item ->
      Option.fold ~none:false ~some:sig_holds (Env.function_sig env item)
  | Member (owner, name) ->
      List.exists
        (fun (m : Env.member) -> m.name = name && sig_holds m.signature)
        (Env.inherent_members env owner)
  | Trait_method (trait, name, _) -> (
      match Env.trait_info env trait with
      | Some info ->
          List.exists
            (fun (m : Env.trait_method) ->
              m.method_name = name && sig_holds m.method_sig)
            info.methods
      | None -> false)
  | Operation (eff, name) -> (
      match Env.effect_info env eff with
      | Some info ->
          List.exists
            (fun (n, (o : Env.operation_sig)) ->
              n = name
              && (List.exists (fun (_, t) -> holds t) o.op_params
                 || holds o.op_ret || row_holds o.op_row))
            info.ops
      | None -> false)

let type_holds env item =
  match Env.type_info env item with
  | Some { def = Record fields; _ } ->
      List.exists (fun (_, t) -> holds t) fields
  | Some { def = Variants vs; _ } ->
      List.exists (fun (_, ps) -> List.exists holds ps) vs
  | Some { def = Builtin; _ } | None -> false

(* A record type or a variant, whose type's parts hold the error type. *)
let built_holds env item =
  match Env.variant env item with
  | Some (ty, _, _) -> type_holds env ty
  | None -> type_holds env item

let rec pattern_meets (p : A.pattern) =
  holds p.pty
  ||
  match p.pat with
  | P_error -> true
  | P_tuple ps | P_variant (_, ps) | P_or ps | P_list (ps, _) ->
      List.exists pattern_meets ps
  | P_record fields -> List.exists (fun (_, p) -> pattern_meets p) fields
  | P_const e -> holds e.ty
  | P_wild | P_bind _ | P_int _ | P_str _ | P_bool _ -> false

let arms_meet arms =
  List.exists (fun (a : A.arm) -> pattern_meets a.pattern) arms

let expr_meets env (e : A.expr) =
  holds e.ty
  ||
  match e.desc with
  | Error -> true
  | Call (callee, _, _, _) | Project (callee, _, _, _) | Callee (callee, _) ->
      callee_holds env callee
  | Record (item, _, _) | Construct (item, _, _) | Constructor (item, _) ->
      built_holds env item
  | Closure (ps, _, _) -> List.exists pattern_meets ps
  | Match (_, arms) -> arms_meet arms
  | Try (_, Some c) -> arms_meet c.arms
  | For (p, _, _) | If_let (p, _, _, _) -> pattern_meets p
  | _ -> false

(* Whether checking a block met the error type: through a name with an error
   elsewhere, or through a declaration whose signature holds it. *)
let meets env block =
  let found = ref false in
  let stmt (s : A.stmt) =
    match s.stmt with
    | Let b | Var b -> if pattern_meets b.pattern then found := true
    | Assign _ | Assert _ | Yield _ | Expr _ -> ()
  in
  Walk.iter_block ~stmt (fun e -> if expr_meets env e then found := true) block;
  !found

(* {1 Marking} *)

(* Every function of the program, under each of its keys. *)
let functions (program : A.program) =
  List.map snd program.functions
  @ List.map snd program.members
  @ List.map snd program.impl_methods
  @ List.map snd program.default_methods

(* Where the user's modules declare their constants, and those of their
   inherent impls, the first of each name. *)
type places = {
  files : (string, string) Hashtbl.t;  (** By module, its file. *)
  constants : (Hir.item, Ast.loc) Hashtbl.t;
  members : (Hir.item * string, Ast.loc) Hashtbl.t;
  impl_members : (Hir.item * Hir.item * string, Ast.loc) Hashtbl.t;
      (** Those of trait impls, by trait (traits.impl-members). *)
}

let places (hir : Hir.program) =
  let p =
    {
      files = Hashtbl.create 64;
      constants = Hashtbl.create 64;
      members = Hashtbl.create 64;
      impl_members = Hashtbl.create 64;
    }
  in
  let first table key loc =
    if not (Hashtbl.mem table key) then Hashtbl.add table key loc
  in
  let const f (d : Hir.decl Hir.node) =
    match d.desc.kind with Const c -> f c.name.desc c.name.loc | _ -> ()
  in
  List.iter
    (fun (m : Hir.module_) ->
      if not m.std then (
        Hashtbl.replace p.files m.name m.file;
        List.iter
          (const (fun name -> first p.constants { Hir.home = m.name; name }))
          m.decls;
        List.iter
          (fun (i : Hir.impl_decl Hir.node) ->
            match (i.desc.self_ty.desc, i.desc.trait_) with
            | Ty_con (owner, _), None ->
                List.iter
                  (const (fun name -> first p.members (owner, name)))
                  i.desc.members
            | Ty_con (owner, _), Some { trait = Trait_ref trait; _ } ->
                List.iter
                  (const (fun name -> first p.impl_members (trait, owner, name)))
                  i.desc.members
            | _ -> ())
          m.impls))
    hir;
  p

let constant_name p (item : Hir.item) =
  Option.bind (Hashtbl.find_opt p.files item.home) (fun file ->
      Option.map (fun loc -> (file, loc)) (Hashtbl.find_opt p.constants item))

let member_name p ((owner : Hir.item), name) =
  Option.bind (Hashtbl.find_opt p.files owner.home) (fun file ->
      Option.map
        (fun loc -> (file, loc))
        (Hashtbl.find_opt p.members (owner, name)))

let impl_member_name p ((_, (owner : Hir.item), _) as key) =
  Option.bind (Hashtbl.find_opt p.files owner.home) (fun file ->
      Option.map (fun loc -> (file, loc)) (Hashtbl.find_opt p.impl_members key))

let constant_loc hir item = constant_name (places hir) item
let member_constant_loc hir owner name = member_name (places hir) (owner, name)

let impl_constant_loc hir trait owner name =
  impl_member_name (places hir) (trait, owner, name)

let named env p (program : A.program) ~errors ~extents ~recovered =
  let names = ref (Names.of_list recovered) in
  let add (file, loc) = names := Names.add (file, loc) !names in
  List.iter
    (fun (d : Diagnostic.t) ->
      Option.iter
        (fun es -> List.iter (fun loc -> add (d.file, loc)) (lying es d))
        (List.assoc_opt d.file extents))
    errors;
  List.iter
    (fun (f : A.fn_def) ->
      match (f.body, Hashtbl.find_opt p.files f.home) with
      | Code b, Some file when meets env b -> add (file, f.at)
      | _ -> ())
    (functions program);
  let constant name (key, (def : A.expr A.definition)) =
    match (def, name key) with
    | Code e, Some at when meets env [ { A.stmt = Expr e; at = e.loc } ] ->
        add at
    | _ -> ()
  in
  List.iter (constant (constant_name p)) program.constants;
  List.iter (constant (member_name p)) program.member_constants;
  List.iter (constant (impl_member_name p)) program.impl_constants;
  !names

let mark env hir (program : A.program) ~errors ~extents ~recovered =
  let p = places hir in
  let names =
    Names.union
      (named env p program ~errors ~extents ~recovered)
      (Names.of_list
         (List.concat_map
            (fun (m : Hir.module_) ->
              if m.std then []
              else List.map (fun loc -> (m.file, loc)) (signature_errors m))
            hir))
  in
  let has at = Names.mem at names in
  let fn (key, (f : A.fn_def)) =
    match (f.body, Hashtbl.find_opt p.files f.home) with
    | (Code _ | Broken), Some file when has (file, f.at) ->
        (key, { f with body = A.Broken })
    | _ -> (key, f)
  in
  let constant name (key, (def : A.expr A.definition)) =
    match (def, name key) with
    | Code _, Some at when has at -> (key, A.Broken)
    | _ -> (key, def)
  in
  {
    program with
    functions = List.map fn program.functions;
    members = List.map fn program.members;
    impl_methods = List.map fn program.impl_methods;
    default_methods = List.map fn program.default_methods;
    constants = List.map (constant (constant_name p)) program.constants;
    member_constants =
      List.map (constant (member_name p)) program.member_constants;
    impl_constants =
      List.map (constant (impl_member_name p)) program.impl_constants;
  }
