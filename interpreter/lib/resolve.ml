(* Name resolution. The standard library is resolved first, since it names no
   module of the program, and then the program, each in four steps:

   1. Each module gets a scope: the items it declares and the names its [use]
      declarations bind, in a type namespace and a value namespace (declarations.namespaces).
   2. Each module's header is checked against the module's name (program.module-header).
   3. Every declaration is resolved into its Hir form, recording the places
      where one module names another. The program's macros are checked
      first, so that each use of one is expanded where it is (macros.uses and macros.expansion).
   4. Those places are checked for cycles (program.no-cycles).

   No error causes another (errors.root-causes). A name with an error resolves to
   an error node, which the type checker gives the error type, and so does
   every use of a name whose declaration is an error of its own name. *)

open Hir
open Resolve_context
open Resolve_scopes
open Resolve_header
open Resolve_decls
open Resolve_cycles

type parsed = Program.source * Ast.module_

(* Every prefix of a dotted name, the name included. *)
let prefixes name =
  let segments = String.split_on_char '.' name in
  List.mapi
    (fun i _ -> dotted (List.filteri (fun j _ -> j <= i) segments))
    segments

(* The macros that a module declares, with the functions their templates
   name (macros.expansion-effects). *)
let macros st home =
  Hashtbl.fold
    (fun (item : item) (m : macro) found ->
      if item.home = home then
        { macro_name = m.decl.name; names = m.named } :: found
      else found)
    st.macros []
  |> List.sort (fun a b -> compare a.macro_name.loc b.macro_name.loc)

(* macros.procedural-declarations, macros.procedural-bodies and macros.meta-tier: a procedural macro, resolved and checked as a
   function of its signature, which makes its module meta. *)
let resolve_proc ctx (item : Ast.item) (d : Ast.decl) (f : Ast.fn_decl) =
  meta ctx;
  let resolved =
    resolve_decl ctx { desc = { d with kind = Fn f }; loc = item.loc }
  in
  (match resolved.desc.kind with
  | Fn r -> Resolve_proc_decls.check_decl ctx f r
  | _ -> ());
  resolved

(* meta.reflection-tier, and c.systems-tier: naming [std.meta] makes a module meta,
   and naming [std.c] makes it systems. *)
let tier_of_use env name ns =
  let mark tiers = if List.mem name tiers then tiers else name :: tiers in
  if ns = "std.meta" then env.st.meta <- mark env.st.meta;
  if ns = "std.c" then env.st.systems <- mark env.st.systems

(* Step 3 *)
let resolve_module env scope (u : unit_) =
  let limits = check_header env.st u in
  let ctx = module_ctx env scope in
  let decls, impls, imports =
    List.fold_left
      (fun (decls, impls, imports) (item : Ast.item) ->
        match item.desc with
        | Use path -> (
            match env.view u.source.package (dotted_path path) with
            | Found ns when Sset.mem ns env.modules ->
                tier_of_use env u.name ns;
                (decls, impls, ns :: imports)
            | _ -> (decls, impls, imports))
        | Decl { kind = Syntax _; _ } | Meta_use _ -> (decls, impls, imports)
        | Decl ({ kind = Macro f; _ } as d) ->
            (resolve_proc ctx item d f :: decls, impls, imports)
        | Decl d ->
            let d = resolve_decl ctx { desc = d; loc = item.loc } in
            (d :: decls, impls, imports)
        | Impl i ->
            let i = { desc = resolve_impl ctx i; loc = item.loc } in
            (decls, i :: impls, imports))
      ([], [], []) u.tree.items
  in
  let impls = List.rev impls in
  check_inherent_members ctx
    (List.map (fun (i : impl_decl node) -> i.desc) impls);
  {
    name = u.name;
    file = u.source.file;
    std = u.std;
    tier =
      (if List.mem u.name env.st.systems then Systems
       else if List.mem u.name env.st.meta then Meta
       else if List.mem u.name env.st.advanced then Advanced
       else Core);
    limits;
    imports = List.sort_uniq String.compare imports;
    decls = List.rev decls;
    impls;
    macros = macros env.st u.name;
    procs =
      List.filter_map
        (fun (item : Ast.item) ->
          match item.desc with
          | Decl { kind = Macro f; _ } -> Some f.name
          | _ -> None)
        u.tree.items;
    unresolved =
      List.filter_map
        (fun (file, loc) -> if file = u.source.file then Some loc else None)
        env.st.unresolved;
    held =
      List.filter_map
        (fun (file, at, name, d) ->
          if file = u.source.file then Some (at, name, d) else None)
        env.st.held;
  }

(* Resolves [units] in [env], whose scopes must include theirs. *)
let resolve_units env scopes units =
  let hir = List.map2 (resolve_module env) scopes units in
  let named =
    Sset.of_list
      (List.filter_map (fun u -> if u.valid then Some u.name else None) units)
  in
  check_cycles env.st named;
  hir

let unit_of ~std ~local valid ((source : Program.source), tree) =
  let name = if valid then dotted source.module_path else source.file in
  { name; local = dotted local; valid; std; source; tree }

(* The names of the items that each module of [units] declares, which other
   modules can name, added to [items]. *)
let items_of items units =
  List.fold_left
    (fun items u ->
      if u.valid then Smap.add u.name (Resolve_imports.declared u.tree) items
      else items)
    items units

let add_scope scopes u scope =
  if u.valid then Smap.add u.name scope scopes else scopes

(* The standard library: its environment, the prelude's scope, and its
   modules. *)
let resolve_std st std =
  let std =
    List.map
      (fun (parsed : parsed) ->
        unit_of ~std:true ~local:(fst parsed).module_path true parsed)
      std
  in
  let std_names = List.map (fun u -> u.name) std in
  let rec std_env =
    {
      st;
      modules = Sset.of_list std_names;
      scopes = Smap.empty;
      namespaces = Sset.of_list (List.concat_map prefixes std_names);
      unnamed = Sset.empty;
      view = (fun _ name -> whole_view std_env name);
      items = items_of Smap.empty std;
    }
  in
  let prelude_unit = List.find (fun u -> u.name = prelude) std in
  let prelude_scope =
    build_scope std_env ~prelude_names:(Sset.empty, Sset.empty) ~is_prelude:true
      prelude_unit
  in
  let std_scopes =
    List.map
      (fun u ->
        if u == prelude_unit then prelude_scope
        else
          build_scope std_env ~prelude_names:(Sset.empty, Sset.empty)
            ~is_prelude:false u)
      std
  in
  let std_env =
    {
      std_env with
      scopes = List.fold_left2 add_scope Smap.empty std std_scopes;
    }
  in
  let std_hir = resolve_units std_env std_scopes std in
  if st.diagnostics <> [] then
    failwith
      ("the standard library has errors: "
      ^ String.concat "; " (List.map Diagnostic.to_string st.diagnostics));
  (std_env, prelude_scope, std_hir)

(* The modules of the program, each name checked (program.module-names): a module
   whose first segment is the name of one of its package's dependencies is
   invalid too (packages.imports). The module of an unreadable file can't be
   named either, which is no error of its name (errors.root-causes). *)
let program_units st (packages : Program.packages) ~unreadable program =
  List.map
    (fun ((source : Program.source), tree) ->
      let local = Program.local_path packages source in
      let deps =
        Option.fold ~none:[]
          ~some:(fun (p : Program.package) -> p.deps)
          (List.nth_opt packages.list source.package)
      in
      let dependency =
        List.exists (fun (d : Program.dep) -> d.dep_name = List.hd local) deps
      in
      let valid = valid_module_path local && not dependency in
      if not valid then
        report st ~file:source.file Code.e0200 { line = 1; col = 1 }
          "`%s` is not a valid module name%s" (dotted local)
          (if dependency then ": the package depends on a package of its name"
           else "");
      let readable = not (List.mem source.file unreadable) in
      unit_of ~std:false ~local (valid && readable) (source, tree))
    program

(* The environment of the program, whose modules can name those of the
   standard library. *)
let program_env std_env program =
  let names valid =
    List.concat_map
      (fun u ->
        if u.valid = valid then prefixes (dotted u.source.module_path) else [])
      program
  in
  let namespaces = Sset.union std_env.namespaces (Sset.of_list (names true)) in
  {
    std_env with
    modules =
      List.fold_left
        (fun modules u -> if u.valid then Sset.add u.name modules else modules)
        std_env.modules program;
    namespaces;
    unnamed = Sset.diff (Sset.of_list (names false)) namespaces;
    items = items_of std_env.items program;
  }

(* The names of the prelude's public items, its types and traits, then its
   variants and functions, which no other module may declare in the same
   namespace (program.prelude-names). *)
let prelude_names (prelude_scope : scope) =
  let public table =
    Smap.fold
      (fun name e names -> if e.pub then Sset.add name names else names)
      table Sset.empty
  in
  ( public prelude_scope.types,
    public
      (Smap.filter_map
         (fun _ -> function Item e -> Some e | _ -> None)
         prelude_scope.values) )

let resolve ?(packages = Program.single) ?(unreadable = []) ?(host = Procs.none)
    ~std program =
  let st =
    {
      diagnostics = [];
      unknown_names = None;
      unresolved = [];
      held = [];
      references = [];
      advanced = [];
      meta = [];
      systems = [];
      next_id = 0;
      macros = Hashtbl.create 8;
      expansions = Hashtbl.create 8;
      chain = [];
      declaring = false;
      named = None;
      constants = Hashtbl.create 16;
      computed = Hashtbl.create 16;
      host;
    }
  in
  let std_env, prelude_scope, std_hir = resolve_std st std in
  let program = program_units st packages ~unreadable program in
  let env = program_env std_env program in
  let env = { env with view = Resolve_view.view packages program env } in
  let prelude_names = prelude_names prelude_scope in
  let scopes =
    List.map (build_scope env ~prelude_names ~is_prelude:false) program
  in
  let env =
    { env with scopes = List.fold_left2 add_scope env.scopes program scopes }
  in
  Resolve_syntax.declare_all env scopes program;
  let hir = resolve_units env scopes program in
  let by_name (a : module_) (b : module_) = String.compare a.name b.name in
  let by_position (a : Diagnostic.t) (b : Diagnostic.t) =
    compare (a.file, a.line, a.col, a.code) (b.file, b.line, b.col, b.code)
  in
  (List.sort by_name (std_hir @ hir), List.sort by_position st.diagnostics)
