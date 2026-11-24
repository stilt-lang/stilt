(* The resolved tree of a single-file test program, and what the names in its
   body refer to. *)

open Stilt

(* The function [t] of the single-file program [text]. *)
let fn_t text =
  let std = Result.get_ok (Driver.parse ~native:true (Program.std ())) in
  let parsed =
    Result.get_ok (Driver.parse (Diagnostics.sources [ ("main.lt", text) ]))
  in
  let program, _ = Resolve.resolve ~std parsed in
  let main = List.find (fun (m : Hir.module_) -> m.name = "main") program in
  main.decls
  @ List.concat_map
      (fun (i : Hir.impl_decl Hir.node) -> i.desc.members)
      main.impls
  |> List.find_map (fun (d : Hir.decl Hir.node) ->
      match d.desc.kind with
      | Fn ({ name = { desc = "t"; _ }; _ } as f) -> Some f
      | _ -> None)
  |> Option.get

let final_expr (f : Hir.fn_decl) =
  match f.body with
  | Some (Body (block, _)) -> (
      match List.rev block with
      | { desc = Expr e; _ } :: _ -> e
      | _ -> invalid_arg "final_expr")
  | _ -> invalid_arg "final_expr"

let rec show (e : Hir.expr) =
  match e.desc with
  | Local v -> "local " ^ v.name
  | Func i -> Printf.sprintf "fn %s.%s" i.home i.name
  | Const i -> Printf.sprintf "const %s.%s" i.home i.name
  | Variant i -> Printf.sprintf "variant %s.%s" i.home i.name
  | Member (Of_type { desc = Ty_con (i, _); _ }, m) ->
      Printf.sprintf "member %s of type %s.%s" m.desc i.home i.name
  | Member (Of_type { desc = Ty_param v; _ }, m) ->
      Printf.sprintf "member %s of type parameter %s" m.desc v.name
  | Member (Of_trait i, m) ->
      Printf.sprintf "member %s of trait %s.%s" m.desc i.home i.name
  | Field (base, m) -> Printf.sprintf "field %s of (%s)" m.desc (show base)
  | Call (f, _) -> Printf.sprintf "call of (%s)" (show f)
  | Error -> "error"
  | _ -> "another expression"

(* Prints what the final expression of [t]'s body refers to. *)
let refers text = print_endline (show (final_expr (fn_t text)))
