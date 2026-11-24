(* Step 1 of name resolution: the scope of each module, which holds the items
   it declares and the names its [use] declarations bind (declarations.namespaces),
   and the names modules may have (program.module-names). *)

open Hir
open Resolve_context

type unit_ = {
  name : string;
  local : string;
  valid : bool;
  std : bool;
  source : Program.source;
  tree : Ast.module_;
}

(* The types of std.prelude that have no declaration, with their numbers of
   type parameters. *)
let builtin_types =
  List.map (fun name -> (name, 0)) primitive_types
  @ [ ("Never", 0); ("List", 1); ("Map", 2) ]

(* A module whose scope is being built: where its errors go, whether it is
   the prelude, the names of the prelude's items in each namespace, and its
   names that clash with them so far. *)
type builder = {
  st : state;
  file : string;
  is_prelude : bool;
  prelude_names : Sset.t * Sset.t;
  mutable shadowed : Sset.t * Sset.t;
}

(* Checks a name the module declares against the primitive types and the
   prelude's names of its namespace (program.prelude-names). *)
let check b namespace (n : name) loc =
  let prelude_types, prelude_values = b.prelude_names in
  let prelude =
    match namespace with Types -> prelude_types | Values -> prelude_values
  in
  if is_primitive n.desc then
    report b.st ~file:b.file Code.e0210 loc "`%s` is a primitive type name"
      n.desc
  else if (not b.is_prelude) && Sset.mem n.desc prelude then (
    report b.st ~file:b.file Code.e0209 loc "`%s` is the name of a prelude item"
      n.desc;
    let types, values = b.shadowed in
    b.shadowed <-
      (match namespace with
      | Types -> (Sset.add n.desc types, values)
      | Values -> (types, Sset.add n.desc values)))

(* A [use] with an error binds a name that no module can have, so the name
   isn't checked. *)
let declare b namespace table (n : name) ?(loc = n.loc) ?(checked = true) v =
  if Smap.mem n.desc table then (
    report b.st ~file:b.file Code.e0208 loc
      "`%s` is already defined in this module" n.desc;
    table)
  else (
    if checked then check b namespace n loc;
    Smap.add n.desc v table)

(* What the [use] declaration of [path] in module [u], at [loc], binds its
   name to. Naming a module records a reference to it. *)
let import ?(meta = false) (env : env) (u : unit_) (loc : loc) path =
  let st = env.st and file = u.source.file in
  let written = dotted_path path in
  match env.view u.source.package written with
  | Found ns ->
      if Sset.mem ns env.modules then
        st.references <-
          { from = u.name; target = ns; file; loc } :: st.references;
      (* tasks.advanced-tier, and tasks.advanced-tier: a module that names [std.task]
         or [std.sync] is advanced. *)
      if
        (ns = "std.task" || ns = "std.sync")
        && not (List.mem u.name st.advanced)
      then st.advanced <- u.name :: st.advanced;
      Import ns
  | Unnamed -> Import_error
  | Foreign package ->
      report st ~file Code.e0218 loc
        "`%s` is a module of the package `%s`, which isn't a dependency of \
         this package"
        written package;
      Import_error
  | Missing ->
      Resolve_imports.missing env ~file ~package:u.source.package ~meta loc path;
      Import_error

(* macros.meta-use: the module that a [meta use] names, by the name it binds,
   which is an import for cycles (program.no-cycles). Two that bind one name
   clash, as two [use] declarations do (declarations.unique-names). *)
let meta_import env (u : unit_) metas (item : Ast.item) =
  match item.desc with
  | Meta_use path -> (
      let n = List.nth path (List.length path - 1) in
      match import ~meta:true env u item.loc path with
      | _ when Smap.mem n.desc metas ->
          report env.st ~file:u.source.file Code.e0208 item.loc
            "`%s` is already named by a `meta use` in this module" n.desc;
          metas
      | Import ns -> Smap.add n.desc ns metas
      | Item _ | Import_error -> metas)
  | Use _ | Decl _ | Impl _ -> metas

(* traits.constructor-traits: the number of arguments of the first [Self] that a type
   applies, if any. *)
let rec self_arity (t : Ast.ty) =
  match t.desc with
  | Ty_named ([ { desc = "Self"; _ } ], (_ :: _ as args)) ->
      Some (List.length args)
  | Ty_named (_, ts) | Ty_tuple ts -> List.find_map self_arity ts
  | Ty_record (fields, _) ->
      List.find_map (fun (f : Ast.field_decl) -> self_arity f.ty) fields
  | Ty_spread t -> self_arity t
  | Ty_fn (_, params, ret, _) ->
      List.find_map self_arity (List.map snd params @ Option.to_list ret)
  | Ty_handler (Effect_named (_, args), ret, _) ->
      List.find_map self_arity (args @ Option.to_list ret)
  | Ty_handler (Effect_async _, ret, _) -> Option.bind ret self_arity
  | Ty_int _ | Ty_bool _ | Ty_macro _ | Ty_splice _ -> None

let member_types (d : Ast.decl Ast.node) =
  match d.desc.kind with
  | Fn f ->
      List.filter_map
        (function
          | Ast.Self_param (_, _, t) -> t | Param (_, _, t, _) -> Some t)
        f.params
      @ Option.to_list f.ret
  | Const c -> [ c.ty ]
  | Type _ | Trait _ | Test _ | Syntax _ | Effect _ | Macro _ -> []

(* What naming a trait needs: its arity as a constructor trait (traits.constructor-traits), its parameters (traits.trait-parameters), and whether it is the advanced tier's
   (traits.advanced-tier). *)
let trait_entry pub (t : Ast.trait_decl) =
  let arity =
    Option.value ~default:0
      (List.find_map self_arity (List.concat_map member_types t.members))
  in
  let beyond_core (d : Ast.decl Ast.node) =
    match d.desc.kind with
    | Fn { params = Self_param _ :: _; _ } -> false
    | Fn _ | Const _ -> true
    | Type _ | Trait _ | Test _ | Syntax _ | Effect _ | Macro _ -> false
  in
  let params = List.map (fun (p : Ast.type_param) -> p.name.desc) t.params in
  let advanced =
    params <> [] || arity > 0 || List.exists beyond_core t.members
  in
  entry ~arity ~params ~advanced Trait_item pub

(* variadics.packs: whether a type's parameters end with its one pack. *)
let valid_pack (params : Ast.type_param list) =
  match List.rev params with
  | last :: others ->
      last.pack && not (List.exists (fun (p : Ast.type_param) -> p.pack) others)
  | [] -> false

(* generics.value-parameters: the positions of a type's value parameters, each with its
   type's name when that is a primitive type's, which resolution checks. *)
let value_positions (params : Ast.type_param list) =
  List.concat
    (List.mapi
       (fun i (p : Ast.type_param) ->
         match p.value with
         | Some { desc = Ty_named ([ n ], []); _ } when is_primitive n.desc ->
             [ (i, Some n.desc) ]
         | Some _ -> [ (i, None) ]
         | None -> [])
       params)

(* generics.value-argument-names: records the constants that a value argument may name, a
   module's own by their items, and an inherent impl's by [Type.NAME], each
   with the module whose scope reads its value. The first of two that share
   a name is the one that names refer to (declarations.unique-names). *)
let record_constants st (u : unit_) =
  let add name (c : Ast.const_decl) =
    let item = { home = u.name; name } in
    if not (Hashtbl.mem st.constants item) then
      Hashtbl.replace st.constants item (c, u.name)
  in
  List.iter
    (fun (item : Ast.item) ->
      match item.desc with
      | Decl { kind = Const c; _ } -> add c.name.desc c
      | Impl
          {
            trait_ = None;
            self_ty = { desc = Ty_named ([ owner ], _); _ };
            members;
            _;
          } ->
          List.iter
            (fun (d : Ast.decl Ast.node) ->
              match d.desc.kind with
              | Const c -> add (owner.desc ^ "." ^ c.name.desc) c
              | _ -> ())
            members
      | _ -> ())
    u.tree.items

(* Declares the names of a declaration at [loc]: its own, and a type's
   variants. *)
let declare_decl b (types, values, tests) (loc : loc)
    ({ pub; kind; _ } : Ast.decl) =
  match kind with
  | Fn f ->
      (types, declare b Values values f.name (Item (entry Fn_item pub)), tests)
  | Const c ->
      ( types,
        declare b Values values c.name (Item (entry Const_item pub)),
        tests )
  | Type t ->
      let arity = List.length t.params in
      let pack = valid_pack t.params in
      let positions = value_positions t.params in
      let types =
        declare b Types types t.name
          (entry ~arity ~pack ~values:positions Type_item pub)
      in
      let variants =
        match t.def with Variants vs -> vs | Record _ | Native _ -> []
      in
      let values =
        List.fold_left
          (fun values (v : Ast.variant_decl) ->
            declare b Values values v.name (Item (entry Variant_item pub)))
          values variants
      in
      (types, values, tests)
  | Trait t -> (declare b Types types t.name (trait_entry pub t), values, tests)
  (* handlers.declaring-effect: an effect is in the type namespace. *)
  | Effect e ->
      let arity = List.length e.params in
      ( declare b Types types e.name (entry ~arity Effect_item pub),
        values,
        tests )
  (* macros.syntax-declarations: a macro is in the value namespace of functions. *)
  | Syntax s ->
      ( types,
        declare b Values values s.name (Item (entry Macro_item pub)),
        tests )
  (* macros.procedural-declarations, and so is a procedural macro. *)
  | Macro f ->
      (types, declare b Values values f.name (Item (entry Proc_item pub)), tests)
  | Test (name, _) ->
      if Sset.mem name tests then (
        report b.st ~file:b.file Code.e0208 loc
          "a test named %S is already declared in this module" name;
        (types, values, tests))
      else (types, values, Sset.add name tests)

(* Step 1: the scope of a module. Every name it declares is checked against
   the primitive types (lexical.primitive-type-names), the prelude (program.prelude-names) and
   the module's other names (declarations.unique-names). *)
let build_scope (env : env) ~prelude_names ~is_prelude (u : unit_) =
  let b =
    {
      st = env.st;
      file = u.source.file;
      is_prelude;
      prelude_names;
      shadowed = (Sset.empty, Sset.empty);
    }
  in
  let builtins =
    if is_prelude then
      List.fold_left
        (fun types (name, arity) ->
          Smap.add name (entry ~arity Type_item true) types)
        Smap.empty builtin_types
    else Smap.empty
  in
  let item (types, values, tests) (item : Ast.item) =
    match item.desc with
    | Use path ->
        let n = List.nth path (List.length path - 1) in
        let value = import env u item.loc path in
        let checked = value <> Import_error in
        (types, declare b Values values n ~loc:item.loc ~checked value, tests)
    | Decl d -> declare_decl b (types, values, tests) item.loc d
    | Impl _ | Meta_use _ -> (types, values, tests)
  in
  let types, values, _ =
    List.fold_left item (builtins, Smap.empty, Sset.empty) u.tree.items
  in
  let metas = List.fold_left (meta_import env u) Smap.empty u.tree.items in
  record_constants env.st u;
  let unknown namespace =
    List.fold_left
      (fun names (item : Ast.item) ->
        match item.desc with
        | Decl { unknown = true; kind; _ } -> (
            match (kind, namespace) with
            | Type t, Types -> Sset.add t.name.desc names
            | Trait t, Types -> Sset.add t.name.desc names
            | Effect e, Types -> Sset.add e.name.desc names
            | Fn f, Values -> Sset.add f.name.desc names
            | Const c, Values -> Sset.add c.name.desc names
            | Syntax s, Values -> Sset.add s.name.desc names
            | _ -> names)
        | _ -> names)
      Sset.empty u.tree.items
  in
  {
    name = u.name;
    file = b.file;
    types;
    values;
    shadowed = b.shadowed;
    metas;
    unknown = (unknown Types, unknown Values);
  }
