(* Patterns, and the names they bind (patterns.pattern-forms). *)

open Hir
open Resolve_context
open Resolve_paths
open Resolve_types

type binder = {
  mutable bound : (string * var) list;
  mutable broken : Sset.t;
  mutable partial : string list;
  mutable failed : bool;
      (* Whether the pattern holds a failed use of a procedural macro (macros.failed-uses). *)
  shared : (string * var) list;
  checked : bool;
}

let binder () =
  {
    bound = [];
    broken = Sset.empty;
    partial = [];
    failed = false;
    shared = [];
    checked = true;
  }

(* The scope that a pattern opens, in which the names it binds are locals. A
   failed use in the pattern binds nothing, so there a name that names
   nothing has the error type and is reported nowhere (macros.failed-uses). *)
let with_bound ctx b =
  let local (name, v) =
    (name, if Sset.mem name b.broken then None else Some v)
  in
  let partial = List.map (fun name -> (name, None)) b.partial in
  {
    ctx with
    locals = List.map local b.bound @ partial @ ctx.locals;
    lost = ctx.lost || b.failed;
  }

let imports_module ctx name =
  match Smap.find_opt name ctx.scope.values with
  | Some (Import _ | Import_error) -> true
  | Some (Item _) | None -> false

(* Binds [n] to [v], unless the pattern already binds that name. Tells
   whether it did. *)
let add ctx b (n : name) v =
  if List.mem_assoc n.desc b.bound then (
    errorf ctx Code.e0208 n.loc "`%s` is already bound here" n.desc;
    false)
  else (
    if b.checked then
      if is_primitive n.desc then (
        (* errors.primitive-type-bindings *)
        errorf ctx Code.e0210 n.loc "`%s` is a primitive type name" n.desc;
        b.broken <- Sset.add n.desc b.broken)
      else if imports_module ctx n.desc then (
        (* program.one-value-namespace *)
        errorf ctx Code.e0207 n.loc "`%s` is the name of an imported module"
          n.desc;
        b.broken <- Sset.add n.desc b.broken)
      else if List.mem_assoc n.desc ctx.value_params then (
        (* generics.value-parameters-in-body: a binding named as a value parameter in scope,
           whose uses have the error type. *)
        errorf ctx Code.e0348 n.loc
          "`%s` is a value parameter here, so no binding takes its name: a \
           type written after it would still name the value parameter"
          n.desc;
        b.broken <- Sset.add n.desc b.broken);
    b.bound <- (n.desc, v) :: b.bound;
    true)

let bind ctx b (n : name) =
  let v =
    match List.assoc_opt n.desc b.shared with
    | Some v -> v
    | None -> fresh ctx n
  in
  ignore (add ctx b n v);
  v

(* A path in a pattern names a variant, a constant, or a constant of a type
   (patterns.floats). *)
let pattern_path ctx (path : name list) ~payload =
  let noun = "a variant or a constant" in
  let no_payload (n : name) desc =
    match payload with
    | None -> desc
    | Some _ ->
        errorf ctx Code.e0212 n.loc "`%s` is a constant, which takes no payload"
          n.desc;
        P_error
  in
  match walk ctx ~want:Values ~noun ~locals:false path with
  | Broken_ref, _, _ -> P_error
  | Item_ref (item, { kind = Variant_item; _ }), _, [] ->
      P_variant (item, Option.value payload ~default:[])
  | Item_ref (item, { kind = Const_item; _ }), last, [] ->
      no_payload last (P_const item)
  | m, last, [ n ] when Option.is_some (as_type m last.loc) ->
      no_payload n (P_assoc_const (Option.get (as_type m last.loc), n))
  | m, last, rest ->
      let what = if rest = [] then noun else "a module" in
      errorf ctx Code.e0212 last.loc "`%s` is %s, not %s" last.desc
        (describe_meaning m) what;
      P_error

(* What a name without a module means in the module's scope, as
   [pattern_path] reads it, but with its error kept for type checking, which
   reports it only if the type the pattern is matched against has no variant
   of that name (patterns.unknown-variants). *)
let fallback ctx (n : name) ~payload =
  let noun = "a variant or a constant" in
  let failure code fmt =
    Printf.ksprintf
      (fun message ->
        Scope_failure (Diagnostic.at ~file:ctx.scope.file code n.loc message))
      fmt
  in
  match lookup ctx Values ~locals:false n.desc with
  | Some (Item_ref (item, { kind = Variant_item; _ })) -> Scope_variant item
  | Some (Item_ref (item, { kind = Const_item; _ })) when not payload ->
      Scope_const item
  | Some (Item_ref (_, { kind = Const_item; _ })) ->
      failure Code.e0212 "`%s` is a constant, which takes no payload" n.desc
  | Some Broken_ref -> Scope_error
  | Some m ->
      failure Code.e0212 "`%s` is %s, not %s" n.desc (describe_meaning m) noun
  | None -> (
      match lookup ctx Types ~locals:true n.desc with
      | Some Broken_ref -> Scope_error
      | Some m ->
          failure Code.e0212 "`%s` is %s, not %s" n.desc (describe_meaning m)
            noun
      | None ->
          let d =
            unknown_diagnostic ctx n.loc ("unknown name `" ^ n.desc ^ "`")
          in
          deferred_name ctx n.desc d;
          Scope_failure d)

(* A field, or a variant that the matched type has, is no name of a scope,
   though a template writes it (macros.hygiene). *)
let unmarked (n : name) = { n with desc = Macro_marks.base n.desc }
let names_of b = List.sort_uniq String.compare (List.map fst b.bound @ b.partial)

let rec resolve_pattern ctx b (p : Ast.pattern) : pattern =
  let desc =
    match p.desc with
    | P_wild -> P_wild
    | P_bind name -> P_bind (bind ctx b { desc = name; loc = p.loc })
    | P_int s -> P_int s
    | P_str s -> P_str s
    | P_bool x -> P_bool x
    | P_tuple ps -> P_tuple (List.map (resolve_pattern ctx b) ps)
    | P_path [ n ] when n.desc <> "Self" ->
        P_bare (unmarked n, [], fallback ctx n ~payload:false)
    | P_variant ([ n ], ps) when n.desc <> "Self" ->
        let ps = List.map (resolve_pattern ctx b) ps in
        P_bare (unmarked n, ps, fallback ctx n ~payload:true)
    | P_path path -> pattern_path ctx path ~payload:None
    | P_variant (path, ps) ->
        let ps = List.map (resolve_pattern ctx b) ps in
        pattern_path ctx path ~payload:(Some ps)
    | P_record (path, fields, rest) -> (
        let field ({ field; pattern } : Ast.field_pattern) =
          { field = unmarked field; pattern = resolve_pattern ctx b pattern }
        in
        match path with
        | Some path -> P_record (record_ty ctx path, List.map field fields, rest)
        (* records.anonymous-patterns and records.advanced-tier *)
        | None ->
            advanced ctx;
            P_fields (List.map field fields, rest))
    | P_list (ps, rest) ->
        let ps = List.map (resolve_pattern ctx b) ps in
        let rest =
          match rest with
          | Exact -> Exact
          | Rest -> Rest
          | Rest_bind n -> Rest_bind (bind ctx b n)
        in
        P_list (ps, rest)
    | P_macro (path, group) -> macro_pattern ctx b p.loc path group
    (* macros.splices *)
    | P_splice s -> Resolve_macros.splice ctx In_pattern s P_wild
    | P_spliced_record (path, fields, _) ->
        Option.iter (fun path -> ignore (record_ty ctx path)) path;
        List.iter
          (function
            | Ast.Field_pattern f -> ignore (resolve_pattern ctx b f.pattern)
            | Spliced_field_pattern (s, p) ->
                Resolve_macros.splice ctx In_name s ();
                ignore (resolve_pattern ctx b p))
          fields;
        P_wild
    | P_or [] -> invalid_arg "Resolve.resolve_pattern"
    | P_or (first :: others) -> P_or (resolve_or ctx b first others)
  in
  { desc; loc = p.loc }

(* macros.uses and macros.expansion: a pattern macro's use, expanded in its place, whose
   names bind as written. *)
and macro_pattern ctx b loc path group =
  match
    Resolve_macros.expand ctx loc path [ group ] Macro_expand.Pattern
      (fun ctx tokens ->
        Macro_expand.parse_pattern ~file:ctx.scope.file ~at:loc tokens)
      (fun ctx p -> resolve_pattern ctx b p)
  with
  | Some p -> p.desc
  | None ->
      if Resolve_procs.names_proc ctx path then b.failed <- true;
      P_error

(* patterns.or-patterns. Each alternative binds its names in a binder of its own,
   and the later ones reuse the first one's variables. Then the or-pattern
   binds, once, each name that every alternative binds. A name that only some
   alternatives bind has the error type wherever it is used. *)
and resolve_or ctx b first others =
  let alternative shared (p : Ast.pattern) =
    let sub =
      {
        bound = [];
        broken = Sset.empty;
        partial = [];
        failed = false;
        shared;
        checked = false;
      }
    in
    (resolve_pattern ctx sub p, sub)
  in
  let first, first_binder = alternative [] first in
  let others =
    List.map
      (fun (p : Ast.pattern) ->
        let resolved, sub = alternative first_binder.bound p in
        if
          names_of sub <> names_of first_binder
          && not (sub.failed || first_binder.failed)
        then
          errorf ctx Code.e0217 p.loc
            "this alternative binds different names from the first";
        (resolved, sub))
      others
  in
  let binders = first_binder :: List.map snd others in
  if List.exists (fun sub -> sub.failed) binders then b.failed <- true;
  let vars =
    List.fold_left
      (fun vars sub ->
        List.fold_left
          (fun vars (name, v) ->
            if List.mem_assoc name vars then vars else vars @ [ (name, v) ])
          vars (List.rev sub.bound))
      [] binders
  in
  let everywhere name =
    List.for_all
      (fun sub ->
        List.mem_assoc name sub.bound && not (Sset.mem name sub.broken))
      binders
  in
  let partial =
    List.filter (fun (name, _) -> not (everywhere name)) vars
    |> List.map fst
    |> List.append (List.concat_map (fun sub -> sub.partial) binders)
  in
  List.iter
    (fun (name, (v : var)) ->
      if everywhere name then ignore (add ctx b { desc = name; loc = v.loc } v))
    vars;
  b.partial <- List.sort_uniq String.compare partial @ b.partial;
  first :: List.map fst others
