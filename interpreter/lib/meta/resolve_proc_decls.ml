(* The declarations of procedural macros (macros.procedural-declarations). *)

open Hir
open Resolve_context

(* macros.procedural-declarations: a macro's parameters take [std.meta]'s input types, only the
   last [meta.Tokens], it gives [meta.Expr], [meta.Pattern] or [meta.Type],
   may raise only [meta.Error], and has no generics and no [without] clause:
   anything else is E0228, at the part that breaks the rule. A type with an
   error breaks none. *)
let check_decl ctx (f : Ast.fn_decl) (resolved : fn_decl) =
  let broken loc what = errorf ctx Code.e0228 loc "a macro %s" what in
  (match f.generics with
  | (Type_param { name; _ } | Row_param name) :: _ ->
      broken name.loc "has no generics"
  | [] -> ());
  Option.iter
    (fun (w : Ast.without) -> broken w.loc "has no `without` clause")
    f.without;
  let last = List.length f.params - 1 in
  List.iteri
    (fun i (p, (r : param)) ->
      match (p, r) with
      | Ast.Self_param (_, loc, _), _ -> broken loc "takes no `self`"
      | Param (_, _, t, _), Param (_, _, ty, _) -> (
          match Procs.input ty with
          | _ when Resolve_types.has_error ty -> ()
          | None ->
              broken t.loc
                "takes `meta.Expr`, `meta.Pattern`, `meta.Type`, `meta.Text`, \
                 `meta.File` or `meta.Tokens`"
          | Some Takes_tokens when i < last ->
              broken t.loc "takes `meta.Tokens` only in its last parameter"
          | Some _ -> ())
      | Param _, Self_param _ -> ())
    (List.combine f.params resolved.params);
  (match (f.ret, resolved.ret) with
  | Some t, Some ty
    when Procs.result ty = None && not (Resolve_types.has_error ty) ->
      broken t.loc "gives `meta.Expr`, `meta.Pattern` or `meta.Type`"
  | _ -> ());
  List.iter
    (function
      | Ast.Row_raise (loc, _) -> (
          match resolved.row.raise with
          | Some
              { desc = Ty_con ({ home = "std.meta"; name = "Error" }, []); _ }
            ->
              ()
          | Some ty when Resolve_types.has_error ty -> ()
          | _ -> broken loc "raises only `meta.Error`")
      | Row_io loc | Row_async loc -> broken loc "performs nothing"
      | Row_var n -> broken n.loc "has no row variable"
      | Row_effect (p, _) -> broken (List.hd p).loc "performs nothing")
    f.row
