(* errors.phases: phases 2 and 3 of checking each body. *)

open Tast

type body = {
  module_ : Hir.module_;
  params : (Ast.mode * Hir.var) list;
  through : Hir.var list;
      (** Its non-escaping parameters (effects.non-escaping-parameters). Tests
          and doc examples have none. *)
  pairs : (Hir.var * label) list;
      (** The row variables its signature pairs with an error type
          (effects.paired-row-variables). Tests and doc examples have none. *)
  passed : (Ast.loc * Types.row * label) list;
      (** What its uses give the row variables that their callees pair
          (effects.passing-to-paired-variables). Tests and doc examples declare
          no row variables, so they need no check. *)
  code : block definition;
  limits : Ast.limit list;
      (** The limits that its module and its own clause set on it: none for a
          test or a doc example (effects.without-panic; facts.without-alloc). *)
  copy : (string * Ast.loc) option;
      (** A function's path (edits.paths) and name, whose body is compared with
          the others (docs.bodies-compared). Other bodies have none. *)
  yields : Ast.loc option;
      (** For a projection, the closing brace of its body, where a path that
          ends without a [yield] is reported (projections.once-on-every-path).
      *)
  key : Implicit_names.key option;
      (** The item whose body it is: none for a test or a doc example. *)
  type_params : Hir.var list;
      (** The type parameters of the item whose body it is, as its signature
          gives them. *)
  unsafe_blocks : Ast.loc list;
      (** Its own [unsafe] blocks: none counted for a test or a doc example,
          which no limit covers (c.without-unsafe). *)
}

(* declarations.typed-holes *)
let holes ~file block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Hole ->
          found :=
            Diagnostic.at ~file Code.w0300 e.loc
              "this hole is code not written yet"
            :: !found
      | _ -> ())
    block;
  List.rev !found

(* The limits on the implicit effects of the body of [f], a function of
   [m]: its module's and its own, each once (effects.without-panic; facts.without-alloc). *)
let fn_limits (m : Hir.module_) (f : fn_def) =
  List.sort_uniq compare
    (List.map (fun (l : Hir.limit Hir.node) -> l.desc) m.limits @ f.limits)

(* Whether [key] is a procedural macro of [m], whose body isn't compared for
   duplicates, since no call can stand in for it in its own module (macros.procedural-bodies and macros.meta-use). *)
let is_proc (m : Hir.module_) = function
  | Implicit_names.Function (i : Hir.item) ->
      List.exists (fun (n : Hir.name) -> n.desc = i.name) m.procs
  | _ -> false

(* The body of a test, a doc example or a property, in the module [m], which no
   limit covers. *)
let test_body m code =
  {
    module_ = m;
    params = [];
    through = [];
    pairs = [];
    passed = [];
    code;
    limits = [];
    copy = None;
    yields = None;
    key = None;
    type_params = [];
    unsafe_blocks = [];
  }

(* Every body of the program, with its module. Tests, doc examples and
   properties are exempt from module limits (effects.without-panic; tests.property-checking). *)
let bodies (hir : Hir.program) (program : program) =
  let find p = List.find (fun (m : Hir.module_) -> p m) hir in
  let fn key path (f : fn_def) =
    let m = find (fun m -> m.name = f.home) in
    {
      module_ = m;
      params = f.params;
      through = f.through;
      pairs = f.pairs;
      passed = f.passed;
      code = f.body;
      limits = fn_limits m f;
      copy =
        (if is_proc m key then None
         else Some (String.concat "." (f.home :: path), f.at));
      yields = f.yields;
      key = Some key;
      type_params = f.type_params;
      unsafe_blocks = f.unsafe_blocks;
    }
  in
  let name (i : Hir.item) = i.name in
  let test file code = test_body (find (fun m -> m.file = file)) code in
  let example_block = function
    | Code claim -> Code [ { stmt = Expr claim; at = claim.loc } ]
    | Native -> Native
    | Broken -> Broken
  in
  List.map
    (fun (i, f) -> fn (Implicit_names.Function i) [ name i ] f)
    program.functions
  @ List.map
      (fun ((ty, m), f) -> fn (Implicit_names.Member (ty, m)) [ name ty; m ] f)
      program.members
  @ List.map
      (fun ((tr, ty, m), f) ->
        fn (Implicit_names.Impl_method (tr, ty, m)) [ name ty; name tr; m ] f)
      program.impl_methods
  @ List.map
      (fun ((tr, m), f) ->
        fn (Implicit_names.Default_method (tr, m)) [ name tr; m ] f)
      program.default_methods
  @ List.map (fun (t : test) -> test t.file t.block) program.tests
  @ List.map
      (fun (e : example) -> test e.file (example_block e.claim))
      program.examples
  @ List.map
      (fun (p : property) -> test p.file (example_block p.closure))
      program.properties

(* c.without-unsafe: each [unsafe] block of a body that [without unsafe] limits,
   which limits its own code alone. *)
let unsafe_errors ~file body =
  if List.mem (Ast.Unsafe : Ast.limit) body.limits then
    List.map
      (fun loc ->
        Diagnostic.at ~file Code.e0204 loc
          "this `unsafe` block runs code that can break the language's \
           guarantees, beyond `without unsafe`")
      body.unsafe_blocks
  else []

(* Phase 2's errors of one body, and phase 3's warnings if it has none. *)
let check_body env effects reflects body block =
  let file = body.module_.file in
  let exhaustive_errors, unreachable = Exhaustive.check env ~file block in
  let errors =
    Marking.errors ~file ~pairs:body.pairs ~passed:body.passed block
    @ Resumes.errors ~file block
    @ Escapes.errors env ~file ~through:body.through block
    @ exhaustive_errors
    @ Modes.errors ~file ~params:body.params block
    @ Views.errors env ~file ~params:body.params block
    @ Option.fold ~none:[]
        ~some:(fun at -> Projections.errors ~file ~at block)
        body.yields
    @ Implicit.limit_errors env effects ~file ~limits:body.limits ~key:body.key
        block
    @ unsafe_errors ~file body
    @ Implicit.lock_errors env effects ~file block
    @ Demands.errors env ~file block
    @ Staging.errors ~file ~params:body.params block
    @ Reflects.errors reflects env ~file ~key:body.key ~own:body.type_params
        block
  in
  if errors <> [] then (errors, [])
  else
    (* effects.catch-alls-need-reason: an arm that can never match gets only that
       warning. *)
    let dead (d : Diagnostic.t) =
      List.exists
        (fun (u : Diagnostic.t) -> u.line = d.line && u.col = d.col)
        unreachable
    in
    let reasons =
      List.filter
        (fun (d : Diagnostic.t) -> not (d.code = Code.w0501 && dead d))
        (Marking.warnings ~file block)
    in
    ([], reasons @ unreachable @ holes ~file block)

(* The function's body that docs.bodies-compared compares, if [body] is one. *)
let candidate body block : Phases_copies.candidate option =
  Option.map
    (fun (path, at) ->
      {
        Phases_copies.file = body.module_.file;
        path;
        at;
        params = List.map snd body.params;
        block;
      })
    body.copy

let check ~std ~text env (hir : Hir.program) (program : program) =
  let limited limit (f : fn_def) =
    List.exists
      (fun (m : Hir.module_) ->
        m.name = f.home && List.mem limit (fn_limits m f))
      hir
  in
  let effects = Implicit.infer env program ~limited in
  let reflects = Reflects.infer env program in
  let checked =
    List.map
      (fun body ->
        match body.code with
        | Native | Broken -> ([], None)
        | Code _ when body.module_.std && not std -> ([], None)
        | Code block -> (
            match
              (check_body env effects reflects body block, body.module_.std)
            with
            | ([], _), true -> ([], None)
            | (errors, _), true ->
                failwith
                  ("the standard library has errors: "
                  ^ String.concat "; " (List.map Diagnostic.to_string errors))
            | ([], warnings), false -> (warnings, candidate body block)
            | (errors, _), false -> (errors, None)))
      (bodies hir program)
  in
  List.concat_map fst checked
  @ Phases_copies.warnings ~text (List.filter_map snd checked)
