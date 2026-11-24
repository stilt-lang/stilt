(* A [use] whose path names no namespace (program.what-use-binds): read as a path in
   code is, it may name an item of a module, which is E0230, and otherwise it
   names nothing, E0205. *)

open Resolve_context

let variant_names names (t : Ast.type_decl) =
  match t.def with
  | Variants vs ->
      List.fold_left
        (fun names (v : Ast.variant_decl) -> Sset.add v.name.desc names)
        names vs
  | Record _ | Native _ -> names

let declared (tree : Ast.module_) =
  List.fold_left
    (fun names (item : Ast.item) ->
      match item.desc with
      | Decl { kind = Fn f | Macro f; _ } -> Sset.add f.name.desc names
      | Decl { kind = Const c; _ } -> Sset.add c.name.desc names
      | Decl { kind = Type t; _ } ->
          variant_names (Sset.add t.name.desc names) t
      | Decl { kind = Trait t; _ } -> Sset.add t.name.desc names
      | Decl { kind = Effect e; _ } -> Sset.add e.name.desc names
      | Decl { kind = Syntax s; _ } -> Sset.add s.name.desc names
      | Decl { kind = Test _; _ } | Use _ | Meta_use _ | Impl _ -> names)
    Sset.empty tree.items

(* The first start of [path], from the shortest, that names a module which
   declares the name after it, as a path in code reads [n.x] as the item [x]
   of [n] (program.what-use-binds), with the names from that one on. *)
let item_import env package (path : Hir.name list) =
  let rec go k =
    if k >= List.length path then None
    else
      let prefix = List.filteri (fun i _ -> i < k) path
      and rest = List.filteri (fun i _ -> i >= k) path in
      let declares ns =
        Sset.mem ns env.modules
        && Sset.mem (List.hd rest).desc
             (Option.value (Smap.find_opt ns env.items) ~default:Sset.empty)
      in
      match env.view package (dotted_path prefix) with
      | Found ns when declares ns -> Some (prefix, rest)
      | _ -> go (k + 1)
  in
  go 1

let missing env ~file ~package ~meta loc path =
  let written = dotted_path path in
  match item_import env package path with
  | Some (prefix, rest) ->
      let keyword = if meta then "meta use" else "use" in
      report env.st ~file Code.e0230 loc
        "`%s` names a module: write `%s %s`, then `%s`" keyword keyword
        (dotted_path prefix)
        (dotted_path (List.nth prefix (List.length prefix - 1) :: rest))
  | None -> report env.st ~file Code.e0205 loc "there is no module `%s`" written
