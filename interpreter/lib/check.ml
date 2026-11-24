(* Type checking. Each body is checked in evaluation order (values.left-to-right),
   with expected types flowing inward where they are known, as in any
   bidirectional checker. Rules whose answer needs every type of the body,
   such as trait bounds, literal ranges and unused values, are recorded as
   they are met and decided at the end of the body, after literals take
   their default types (numbers.literal-defaults).

   This module walks the program, and the [Check_*] modules check its
   bodies, one concern each. *)

module T = Types
module A = Tast
open Check_state
open Check_bodies
open Check_constants

(* What checking the program has found so far, latest first. *)
type found = {
  mutable errors : Diagnostic.t list;
  mutable std_errors : Diagnostic.t list;
  mutable functions : (Hir.item * A.fn_def) list;
  mutable members : ((Hir.item * string) * A.fn_def) list;
  mutable impl_methods : ((Hir.item * Hir.item * string) * A.fn_def) list;
  mutable default_methods : ((Hir.item * string) * A.fn_def) list;
  mutable default_constants : ((Hir.item * string) * A.expr A.definition) list;
  mutable constants : (Hir.item * A.expr A.definition) list;
  mutable member_constants : ((Hir.item * string) * A.expr A.definition) list;
  mutable impl_constants :
    ((Hir.item * Hir.item * string) * A.expr A.definition) list;
  mutable tests : A.test list;
  mutable examples : A.example list;
  mutable properties : A.property list;
  mutable valued : (constant * Hir.module_ * Ast.loc * constant list) list;
      (* The constants that have values, for [constant_cycles]. *)
}

let collect found (m : Hir.module_) es =
  if m.std then found.std_errors <- es @ found.std_errors
  else found.errors <- es @ found.errors

let constant ?bounds ?self env found m (c : Hir.const_decl) value key =
  let value, named, es = check_constant ?bounds ?self env m c value in
  collect found m es;
  (match (value, key) with
  | (Code _ | Broken), Some key ->
      found.valued <- (key, m, c.name.loc, named) :: found.valued
  | _ -> ());
  value

let examples_of env found (m : Hir.module_) (decl : Hir.decl Hir.node) =
  List.iter
    (function
      | Hir.Doc_example e ->
          let claim, es = check_example env m e in
          collect found m es;
          found.examples <-
            { A.file = m.file; loc = e.loc; claim } :: found.examples
      | Hir.Doc_property (text, e) ->
          let closure, es = Check_properties.check_property env m e in
          collect found m es;
          found.properties <-
            { A.file = m.file; loc = e.loc; text; closure } :: found.properties
      | Doc_text _ -> ())
    decl.desc.doc

(* The default methods and constants of [trait], which declares [members].
   Their [Self] is bounded by the trait, with its parameters as its arguments
   (traits.trait-parameters and traits.trait-constants). *)
let default_members env found m trait members =
  Option.iter
    (fun (info : Env.trait_info) ->
      let self = T.Param info.self_param in
      let args = List.map (fun v -> T.Param v) info.params in
      let bounds = [ (info.self_param, [ { Env.trait; args } ]) ] in
      List.iter
        (fun (member : Hir.decl Hir.node) ->
          examples_of env found m member;
          match member.desc.kind with
          | Fn ({ body = Some body; _ } as f) ->
              let s = Env.signature ~self ~self_ty:self ~outer:[] f in
              let def, es = check_fn env m ~bounds ~self:(Some self) s f body in
              collect found m es;
              found.default_methods <-
                ((trait, f.name.desc), def) :: found.default_methods
          | Const ({ value = Some value; _ } as c) ->
              let def = constant ~bounds ~self env found m c value None in
              found.default_constants <-
                ((trait, c.name.desc), def) :: found.default_constants
          | Fn { body = None; _ }
          | Const { value = None; _ }
          | Type _ | Trait _ | Test _ | Effect _ ->
              ())
        members)
    (Env.trait_info env trait)

let check_decl env found (m : Hir.module_) (decl : Hir.decl Hir.node) =
  let item (n : Hir.name) = { Hir.home = m.name; name = n.desc } in
  examples_of env found m decl;
  match decl.desc.kind with
  | Fn f -> (
      let s = Env.signature ~outer:[] f in
      match f.body with
      | Some body ->
          let def, es = check_fn env m ~bounds:[] ~self:None s f body in
          collect found m es;
          found.functions <- (item f.name, def) :: found.functions
      | None when decl.desc.foreign ->
          found.functions <- (item f.name, foreign_fn m s f) :: found.functions
      | None -> ())
  | Const ({ value = Some value; _ } as c) ->
      let value = constant env found m c value (Some (Global (item c.name))) in
      found.constants <- (item c.name, value) :: found.constants
  (* errors.broken-parts: a constant whose part breaks after its [=] has no
     value, and reading it panics (program.bodies-with-errors). *)
  | Const { value = None; name; _ } ->
      found.constants <- (item name, A.Broken) :: found.constants
  | Test (name, block) ->
      let block, es = check_test env m decl.loc block in
      collect found m es;
      found.tests <-
        { A.name; file = m.file; loc = decl.loc; block } :: found.tests
  | Trait t -> default_members env found m (item t.name) t.members
  | Type _ | Effect _ -> ()

let check_impl env found (m : Hir.module_) (impl : Hir.impl_decl Hir.node) =
  let i = impl.desc in
  let generics = Env.bounds_of i.generics in
  let self_ty = Env.of_hir i.self_ty in
  let owner = match self_ty with Con (item, _) -> Some item | _ -> None in
  let trait_ =
    match i.trait_ with Some { trait = Trait_ref t; _ } -> Some t | _ -> None
  in
  List.iter
    (fun (member : Hir.decl Hir.node) ->
      examples_of env found m member;
      match member.desc.kind with
      | Fn f ->
          Option.iter
            (fun body ->
              let s = Env.signature ~self_ty ~outer:generics f in
              let def, es = check_fn env m ~bounds:[] ~self:None s f body in
              collect found m es;
              Option.iter
                (fun owner ->
                  let name = f.name.desc in
                  match trait_ with
                  | Some trait ->
                      found.impl_methods <-
                        ((trait, owner, name), def) :: found.impl_methods
                  | None ->
                      found.members <- ((owner, name), def) :: found.members)
                owner)
            f.body
      | Const ({ value = Some value; _ } as c) ->
          Option.iter
            (fun owner ->
              let name = c.name.desc in
              match trait_ with
              | Some trait ->
                  let key = Of_impl (trait, owner, name) in
                  let value = constant env found m c value (Some key) in
                  found.impl_constants <-
                    ((trait, owner, name), value) :: found.impl_constants
              | None ->
                  let key = Assoc (owner, name) in
                  let value = constant env found m c value (Some key) in
                  found.member_constants <-
                    ((owner, name), value) :: found.member_constants)
            owner
      | Const { value = None; _ } -> ()
      | Type _ | Trait _ | Test _ | Effect _ -> ())
    i.members

let check env (program : Hir.program) =
  let found =
    {
      errors = [];
      std_errors = [];
      functions = [];
      members = [];
      impl_methods = [];
      default_methods = [];
      default_constants = [];
      constants = [];
      member_constants = [];
      impl_constants = [];
      tests = [];
      examples = [];
      properties = [];
      valued = [];
    }
  in
  List.iter
    (fun (m : Hir.module_) ->
      List.iter (check_decl env found m) m.decls;
      List.iter (check_impl env found m) m.impls)
    program;
  List.iter
    (fun (m, d) -> collect found m [ d ])
    (constant_cycles (List.rev found.valued));
  if found.std_errors <> [] then
    failwith
      ("the standard library has errors: "
      ^ String.concat "; " (List.map Diagnostic.to_string found.std_errors));
  ( {
      A.functions = List.rev found.functions;
      members = List.rev found.members;
      impl_methods = List.rev found.impl_methods;
      default_methods = List.rev found.default_methods;
      default_constants = List.rev found.default_constants;
      constants = List.rev found.constants;
      member_constants = List.rev found.member_constants;
      impl_constants = List.rev found.impl_constants;
      tests = List.rev found.tests;
      examples = List.rev found.examples;
      properties = List.rev found.properties;
    },
    found.errors )
