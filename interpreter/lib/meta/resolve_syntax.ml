(* The declarations of macros (macros.syntax-declarations, macros.patterns and macros.templates). *)

open Hir
open Resolve_context

(* macros.checked-templates: each arm's template parsed as an expression and as a pattern,
   with each fragment standing as a form of its kind, if it is one. *)
let forms ctx (arm : Ast.macro_arm) =
  let block = Option.map (fun ((n : name), _) -> (n.desc, "block")) arm.block in
  let kinds = Macro_check.fragments arm.pattern @ Option.to_list block in
  let file = ctx.scope.file and at = (List.hd arm.template).loc in
  let holes form = Macro_expand.holes form kinds arm.template in
  ( Result.to_option (Macro_expand.parse_expr ~file ~at (holes Expr)),
    Result.to_option (Macro_expand.parse_pattern ~file ~at (holes Pattern)) )

(* macros.checked-templates: the names an expression's template writes, or else a pattern's,
   resolve where the macro is declared. *)
let resolve_names ctx = function
  | Some e, _ -> ignore (Resolve_exprs.resolve_expr ctx e)
  | None, Some p ->
      ignore
        (Resolve_patterns.resolve_pattern ctx (Resolve_patterns.binder ()) p)
  | None, None -> ()

(* Resolves the templates, with one E0211 for each name that doesn't
   resolve, where it is first written. Tells whether they have no error, and
   gives the functions they name (macros.expansion-effects). *)
let resolve_templates ctx forms =
  let st = ctx.env.st in
  let before = st.diagnostics and outer = st.unknown_names in
  st.unknown_names <- Some [];
  st.declaring <- true;
  st.named <- Some [];
  List.iter (resolve_names ctx) forms;
  let found = Option.value st.unknown_names ~default:[] in
  let named = Option.value st.named ~default:[] in
  st.unknown_names <- outer;
  st.declaring <- false;
  st.named <- None;
  let first = Hashtbl.create 8 in
  List.iter
    (fun (u : unknown) ->
      let (d : Diagnostic.t) = u.diagnostic in
      match Hashtbl.find_opt first u.written with
      | Some (e : Diagnostic.t)
        when compare (e.line, e.col) (d.line, d.col) <= 0 ->
          ()
      | _ -> Hashtbl.replace first u.written d)
    found;
  Hashtbl.iter (fun _ d -> st.diagnostics <- d :: st.diagnostics) first;
  (st.diagnostics == before, List.rev named)

(* macros.checked-templates: a template that is neither an expression nor a pattern. *)
let neither ctx (arm : Ast.macro_arm) = function
  | None, None ->
      errorf ctx Code.e0221 (List.hd arm.template).loc
        "this template is neither an expression nor a pattern";
      true
  | _ -> false

let declare ctx (s : Ast.syntax_decl) =
  (* macros.advanced-tier *)
  advanced ctx;
  let st = ctx.env.st in
  let item = { home = ctx.scope.name; name = s.name.desc } in
  if not (Hashtbl.mem st.macros item) then (
    let errors = List.concat_map Macro_check.check_arm s.arms in
    List.iter
      (fun (e : Macro_check.error) -> errorf ctx e.code e.loc "%s" e.message)
      errors;
    let forms = if errors = [] then List.map (forms ctx) s.arms else [] in
    let broken =
      errors = [] && List.exists Fun.id (List.map2 (neither ctx) s.arms forms)
    in
    let usable, named =
      if errors = [] && not broken then resolve_templates ctx forms
      else (false, [])
    in
    let all f =
      usable && List.for_all (fun form -> Option.is_some (f form)) forms
    in
    Hashtbl.add st.macros item
      {
        decl = s;
        home = ctx.scope.name;
        usable;
        expr = all fst;
        pattern = all snd;
        named;
      })

let declare_all env scopes (units : Resolve_scopes.unit_ list) =
  List.iter2
    (fun scope (u : Resolve_scopes.unit_) ->
      let ctx = module_ctx env scope in
      List.iter
        (fun (item : Ast.item) ->
          match item.desc with
          | Decl { kind = Syntax s; unknown = false; _ } -> declare ctx s
          | _ -> ())
        u.tree.items)
    scopes units
