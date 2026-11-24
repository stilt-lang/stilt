(* What names and paths refer to: lookups in a module's scope (declarations.name-lookup), and walks through the namespaces of modules (program.visibility and program.namespaces). *)

open Hir
open Resolve_context

let child ns (n : name) = ns ^ "." ^ n.desc

(* Lookups *)

type meaning =
  | Var_ref of var
  | Param_ref of var
  | Self_ref of ty
  | Item_ref of item * entry
  | Namespace_ref of string
  | Broken_ref

(* [Self], which only impl and trait blocks define (traits.impl-blocks). *)
let self_type ctx loc =
  match ctx.self with
  | Impl_self t -> Self_ref { t with loc }
  | Trait_self -> Self_ref { desc = Ty_self; loc }
  | No_self ->
      errorf ctx Code.e0215 loc "`Self` exists only in impl and trait blocks";
      Broken_ref

(* The item [name] of module [ns], in one namespace. *)
let find ctx namespace ns name =
  Option.bind (Smap.find_opt ns ctx.env.scopes) (fun scope ->
      match namespace with
      | Types -> Smap.find_opt name scope.types
      | Values -> (
          match Smap.find_opt name scope.values with
          | Some (Item e) -> Some e
          | Some (Import _ | Import_error) | None -> None))

let in_prelude ctx namespace name =
  match find ctx namespace prelude name with
  | Some e when e.pub -> Some (Item_ref ({ home = prelude; name }, e))
  | _ -> None

(* What [name] means where the context is, in one namespace. *)
let rec lookup ctx namespace ~locals name =
  if Macro_marks.is_hole name then Some Broken_ref
  else
    match Macro_marks.split name with
    | Some (base, id) when not (locals && List.mem_assoc name ctx.locals) ->
        declared ctx id namespace base
    | _ -> lookup_here ctx namespace ~locals name

(* macros.hygiene: a name that a template writes, and doesn't bind, resolves
   among the items and imports of the module that declares its macro. *)
and declared ctx id namespace name =
  match Hashtbl.find_opt ctx.env.st.expansions id with
  | None -> Some Broken_ref
  | Some home -> (
      match Smap.find_opt home ctx.env.scopes with
      | None -> Some Broken_ref
      | Some scope ->
          let scope = { scope with file = ctx.scope.file } in
          let there = { (module_ctx ctx.env scope) with expanding = true } in
          lookup there namespace ~locals:false name)

and lookup_here ctx namespace ~locals name =
  let types, values = ctx.scope.shadowed in
  let unknown_types, unknown_values = ctx.scope.unknown in
  let types = Sset.union types unknown_types
  and values = Sset.union values unknown_values in
  let here = { home = ctx.scope.name; name } in
  match namespace with
  | Types -> (
      match List.assoc_opt name ctx.type_params with
      | Some v -> Some (Param_ref v)
      | None when Sset.mem name types -> Some Broken_ref
      | None -> (
          match Smap.find_opt name ctx.scope.types with
          | Some e -> Some (Item_ref (here, e))
          | None -> in_prelude ctx Types name))
  | Values -> (
      match List.assoc_opt name (if locals then ctx.locals else []) with
      | Some (Some v) -> Some (Var_ref v)
      | Some None -> Some Broken_ref
      | None when Sset.mem name values -> Some Broken_ref
      | None -> (
          match Smap.find_opt name ctx.scope.values with
          | Some (Item e) -> Some (Item_ref (here, e))
          | Some (Import ns) -> Some (Namespace_ref ns)
          | Some Import_error -> Some Broken_ref
          | None -> in_prelude ctx Values name))

let describe_meaning = function
  | Var_ref _ -> "a variable"
  | Param_ref _ | Self_ref _ -> "a type"
  | Item_ref (_, e) -> describe e.kind
  | Namespace_ref _ -> "a module"
  | Broken_ref -> "nothing"

let other = function Types -> Values | Values -> Types

(* Paths *)

(* E0212 for the name [n], which is [what] and not [noun]. *)
let not_a ctx ~noun (n : name) what =
  errorf ctx Code.e0212 n.loc "`%s` is %s, not %s" n.desc what noun

(* Reports the first name [n] of a path, which means nothing in [namespace],
   with [misplaced] when it means something in the other: a value parameter,
   which hides an item of its name (generics.value-parameters-in-body), is a value there. *)
let missing_here ctx ~misplaced (n : name) namespace =
  if namespace = Types && List.mem_assoc n.desc ctx.value_params then
    misplaced n "a value parameter"
  else
    match lookup ctx (other namespace) ~locals:true n.desc with
    | Some Broken_ref -> ()
    | Some m -> misplaced n (describe_meaning m)
    | None -> unknown_name ctx ~name:n.desc n.loc "unknown name `%s`" n.desc

(* Whether [name] is declared only by name in module [ns], in [namespace] or,
   for a name followed by more names, in either (errors.broken-parts). *)
let unknown ctx ns namespace name =
  match Smap.find_opt ns ctx.env.scopes with
  | None -> false
  | Some scope -> (
      let types, values = scope.unknown in
      match namespace with
      | Types -> Sset.mem name types || Sset.mem name values
      | Values -> Sset.mem name values)

(* Whether the context can name [e], the item [n] of module [ns], with a path
   that starts at [start]. Naming another module's item records a reference
   to that module. *)
let accessible ctx ~start ns (n : name) e =
  let current = ctx.scope.name in
  if ns = current then true
  else (
    ctx.env.st.references <-
      { from = current; target = ns; file = ctx.scope.file; loc = start }
      :: ctx.env.st.references;
    (* views.std-view: a module that names a view type is in the advanced
       tier, and so is one that names [Lazy] (polymorphism.lazy-values). *)
    if
      (ns = "std.view" && List.mem n.desc [ "View"; "Iter" ])
      || (ns = "std.lazy" && n.desc = "Lazy")
    then advanced ctx;
    if not e.pub then
      errorf ctx Code.e0213 n.loc "`%s` is private to module `%s`" (child ns n)
        ns;
    e.pub)

(* Resolves the names of [path] for as long as they name namespaces, the
   first name lexically and each later one in the namespace before it
   (program.namespaces). Returns what the first name that isn't a namespace
   means, that name, and the names after it.

   A name followed by more names is read as a type first, then as a value
   (declarations.name-lookup). The last name is read in [want], and named [noun] in
   errors, where [misplaced] reports one that names something else. Naming an
   item of another module records a reference from the path's first name, and
   needs the item to be visible (program.visibility). An item that isn't visible
   means nothing, so the names after it cause no further error (errors.root-causes). *)
let walk ctx ~want ~noun ?(misplaced = not_a ctx ~noun) ~locals
    (path : name list) =
  let start = (List.hd path).loc in
  (* The path as written, up to [s]. *)
  let written (s : name) =
    let rec upto = function
      | [] -> []
      | (n : name) :: rest -> if n == s then [ n ] else n :: upto rest
    in
    dotted_path (upto path)
  in
  let rec inside ns = function
    | [] -> invalid_arg "Resolve.walk"
    | (s : name) :: rest -> (
        let namespace = if rest = [] then want else Types in
        let found =
          match find ctx namespace ns s.desc with
          | Some e -> Some e
          | None when rest <> [] -> find ctx Values ns s.desc
          | None -> None
        in
        match found with
        | Some _ when unknown ctx ns namespace s.desc -> (Broken_ref, s, [])
        | Some e when accessible ctx ~start ns s e ->
            (Item_ref ({ home = ns; name = s.desc }, e), s, rest)
        | Some _ -> (Broken_ref, s, [])
        | None when Sset.mem (child ns s) ctx.env.namespaces ->
            if rest = [] then (Namespace_ref (child ns s), s, [])
            else inside (child ns s) rest
        | None when Sset.mem (child ns s) ctx.env.unnamed -> (Broken_ref, s, [])
        | None ->
            (match find ctx (other namespace) ns s.desc with
            | Some e -> misplaced { s with desc = child ns s } (describe e.kind)
            | None when Sset.mem ns ctx.env.modules ->
                unknown_name ctx ~name:(written s) s.loc
                  "module `%s` has no item `%s`" ns s.desc
            | None ->
                unknown_name ctx ~name:(written s) s.loc
                  "there is no module `%s`" (child ns s));
            (Broken_ref, s, []))
  in
  match path with
  | [] -> invalid_arg "Resolve.walk"
  | first :: rest -> (
      let meaning =
        if first.desc = "Self" then Some (self_type ctx first.loc)
        else if rest = [] then lookup ctx want ~locals first.desc
        else
          match lookup ctx Types ~locals first.desc with
          | Some m -> Some m
          | None -> lookup ctx Values ~locals first.desc
      in
      match meaning with
      | Some (Namespace_ref ns) when rest <> [] -> inside ns rest
      | Some m -> (m, first, rest)
      | None when ctx.lost -> (Broken_ref, first, [])
      | None ->
          missing_here ctx ~misplaced first (if rest = [] then want else Types);
          (Broken_ref, first, []))

(* The meaning of a path that must end at its last name, since only modules
   hold items in a path, and that name. *)
let walk_to_end ctx ~want ~noun path =
  match walk ctx ~want ~noun ~locals:false path with
  | Broken_ref, last, _ -> (Broken_ref, last)
  | m, last, [] -> (m, last)
  | m, (last : name), _ :: _ ->
      errorf ctx Code.e0212 last.loc "`%s` is %s, not a module" last.desc
        (describe_meaning m);
      (Broken_ref, last)

let wrong_kind ctx (last : name) m noun =
  errorf ctx Code.e0212 last.loc "`%s` is %s, not %s" last.desc
    (describe_meaning m) noun
