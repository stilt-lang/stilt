(* The effects and capabilities that packages perform, the [unsafe] blocks
   they hold, and the grants of their manifests (packages.grants, packages.own-effects, packages.ungranted-effects and packages.running-with-ungranted-effect;
   facts.capability-grants, facts.own-capabilities and facts.ungranted-capabilities; c.granting-unsafe). A package's own
   code performs [io] when one of its functions or methods, or a closure in
   one, calls or names a function of another package whose declared row holds
   [io]. It has a capability when what it names has the capability, and it
   performs [io] without one when what it names performs [io] and has none.
   The items a body names are those that its implicit effects follow (facts.inference and facts.calls-through-function-values), so a call through a function value names nothing. A body
   with an error performs no effect of its own. *)

open Implicit_names
open Grants_messages

type own = {
  package : int;
  def : Tast.fn_def option;
      (** The function, or [None] for a macro, whose templates name items as the
          package's own code does (macros.expansion-effects). *)
  home : string;
  at : Ast.loc;
  path : string;  (** Its path (edits.paths). *)
  facts : (fact * (key * Ast.loc)) list;
      (** Each fact of its own code, with the first item it names that causes it
          and where. *)
}

type t = {
  package_of_module : string -> int option;
      (** The package of a module of the program; [None] for [std]'s. *)
  own : own list;
      (** The functions whose own code performs [io], with their packages, in
          the order of their modules' paths and then of their source. *)
}

let performs_io env key =
  let signature =
    match key with
    | Impl_method (trait, _, name) | Default_method (trait, name) ->
        Implicit_names.signature env (Built_in (trait, name))
    | _ -> Implicit_names.signature env key
  in
  match signature with Some s -> s.row.io | None -> false

(* Whether the item that [key] names is declared in the package [p]. An impl
   lies in its trait's module or its type's, and a package can name only the
   traits and types of its own and of its dependencies, so an impl whose trait
   or type is the package's is the package's. *)
let in_package package_of_module p = function
  | Function item | Member (item, _) | Default_method (item, _) ->
      package_of_module item.home = Some p
  | Impl_method (trait, owner, _) ->
      package_of_module trait.home = Some p
      || package_of_module owner.home = Some p
  | Built_in _ -> true

(* edits.paths *)
let path (f : Tast.fn_def) = function
  | Function item -> f.home ^ "." ^ item.name
  | Member (owner, name) -> String.concat "." [ f.home; owner.name; name ]
  | Impl_method (trait, owner, name) ->
      String.concat "." [ f.home; owner.name; trait.name; name ]
  | Default_method (trait, name) | Built_in (trait, name) ->
      String.concat "." [ f.home; trait.name; name ]

(* The facts that naming [k], an item of another package, gives (facts.own-capabilities). *)
let facts_of env capabilities k =
  match capabilities k with
  | [] when performs_io env k -> [ Bare ]
  | caps -> List.map (fun c -> Has c) caps

(* The facts of what code of the package [p] names, each with its first
   cause. *)
let named_facts env capabilities package_of_module p named =
  List.fold_left
    (fun found (k, loc) ->
      if in_package package_of_module p k then found
      else
        List.fold_left
          (fun found fact ->
            if List.mem_assoc fact found then found
            else found @ [ (fact, (k, loc)) ])
          found
          (facts_of env capabilities k))
    [] named

(* macros.expansion-effects: the functions that the quotes of a body name, which
   are its package's own code, as a template's are. *)
let quoted block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : Tast.expr) ->
      match e.desc with
      | Quote q ->
          found :=
            List.rev_append
              (List.map (fun (item, loc) -> (Function item, loc)) q.names)
              !found
      | _ -> ())
    block;
  List.rev !found

(* The facts of a body of the package [p], each with its first cause. *)
let own_facts env capabilities package_of_module p block =
  named_facts env capabilities package_of_module p
    (List.concat_map
       (fun (s : Implicit_sites.site) -> List.map (fun k -> (k, s.loc)) s.names)
       (Implicit_sites.sites env Implicit_sites.no_in_place block)
    @ quoted block)

(* c.unsafe-in-api and c.granting-unsafe: a body that holds an [unsafe] block, its first
   block the cause. *)
let unsafe_fact key (f : Tast.fn_def) =
  match f.unsafe_blocks with
  | [] -> []
  | first :: _ -> [ (Unsafe_code, (key, first)) ]

(* macros.expansion-effects: the facts of the functions that a package's macros
   name, which are the package's as its functions' are. *)
let macro_facts env capabilities package_of_module (hir : Hir.program) =
  List.concat_map
    (fun (m : Hir.module_) ->
      match package_of_module m.name with
      | None -> []
      | Some p ->
          List.filter_map
            (fun (macro : Hir.macro) ->
              let named =
                List.map (fun (item, loc) -> (Function item, loc)) macro.names
              in
              match named_facts env capabilities package_of_module p named with
              | [] -> None
              | facts ->
                  Some
                    {
                      package = p;
                      def = None;
                      home = m.name;
                      at = macro.macro_name.loc;
                      path = m.name ^ "." ^ macro.macro_name.desc;
                      facts;
                    })
            m.macros)
    hir

let find env hir (program : Tast.program) package_of_module =
  let capabilities = Implicit.capabilities env program in
  let own =
    List.filter_map
      (fun (key, (f : Tast.fn_def)) ->
        match (f.body, package_of_module f.home) with
        | Code block, Some p -> (
            match
              own_facts env capabilities package_of_module p block
              @ unsafe_fact key f
            with
            | [] -> None
            | facts ->
                Some
                  {
                    package = p;
                    def = Some f;
                    home = f.home;
                    at = f.at;
                    path = path f key;
                    facts;
                  })
        | _ -> None)
      (Implicit.bodies program)
    @ macro_facts env capabilities package_of_module hir
  in
  let order (o : own) = (o.home, o.at.line, o.at.col) in
  {
    package_of_module;
    own = List.stable_sort (fun a b -> compare (order a) (order b)) own;
  }

(* The facts of a package's own code, capabilities in the order of facts.capabilities, then [io] without one, each with the first function that has it. *)
let package_facts t p =
  List.filter_map
    (fun fact ->
      List.find_opt
        (fun o -> o.package = p && List.mem_assoc fact o.facts)
        t.own
      |> Option.map (fun o -> (fact, o)))
    (List.map (fun c -> Has c) Capability.all @ [ Bare; Unsafe_code ])

let granted (d : Program.dep) = function
  | Has c -> d.may_io || List.mem c d.may
  | Bare -> d.may_io
  | Unsafe_code -> d.may_unsafe

let diagnostics t (packages : Program.packages) =
  List.concat_map
    (fun (q : Program.package) ->
      List.concat_map
        (fun (d : Program.dep) ->
          match (q.manifest, d.target) with
          | Some file, Some target ->
              let facts = package_facts t target in
              List.filter_map
                (fun (fact, o) ->
                  if granted d fact then None
                  else
                    Some
                      (Diagnostic.at ~file Code.e0608 d.key
                         (ungranted d.dep_name ~facts:(List.map fst facts) fact
                            o.path (List.assoc fact o.facts))))
                facts
          | _ -> [])
        q.deps)
    packages.list

(* The facts of packages that a manifest names without granting them (packages.running-with-ungranted-effect). *)
let ungranted t (packages : Program.packages) =
  List.concat_map
    (fun (q : Program.package) ->
      List.concat_map
        (fun (d : Program.dep) ->
          match d.target with
          | Some target ->
              List.filter_map
                (fun (fact, _) ->
                  if granted d fact then None else Some (target, fact))
                (package_facts t target)
          | None -> [])
        q.deps)
    packages.list

(* [program] with each function of a package whose own code has a fact that
   a manifest doesn't grant it replaced by [Broken], which panics with
   [check-error] when it is called (packages.running-with-ungranted-effect; facts.ungranted-capabilities). *)
let break t packages (program : Tast.program) =
  let ungranted = ungranted t packages in
  let broken (f : Tast.fn_def) =
    List.exists
      (fun o ->
        Option.fold ~none:false ~some:(fun d -> d == f) o.def
        && List.exists
             (fun (fact, _) -> List.mem (o.package, fact) ungranted)
             o.facts)
      t.own
  in
  let fn (key, (f : Tast.fn_def)) =
    if broken f then (key, { f with body = Tast.Broken }) else (key, f)
  in
  {
    program with
    functions = List.map fn program.functions;
    members = List.map fn program.members;
    impl_methods = List.map fn program.impl_methods;
    default_methods = List.map fn program.default_methods;
  }
