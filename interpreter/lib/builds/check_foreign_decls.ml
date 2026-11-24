(* The foreign functions of c.foreign-functions and c.types-c-takes: what C can take of a signature (c.foreign-functions and c.types-c-takes). The parts that a foreign function has no place for are read from
   the syntax, where they are written, and its types as they resolve. *)

open Ast

let error ~file loc message = Diagnostic.at ~file Code.e0353 loc message

(* c.types-c-takes: the types C takes, [c.Str] among them, and [()] as a result only. *)
let c_takes ~result (t : Hir.ty) =
  match t.desc with
  | Ty_error -> true
  | Ty_tuple [] -> result
  | Ty_con ({ home = "std.c"; name = "Str" }, []) -> true
  | _ -> Check_foreign.c_holds (Env.of_hir t)

let generic_loc = function Type_param p -> p.name.loc | Row_param n -> n.loc

let row_loc = function
  | Row_io _ -> None
  | Row_raise (loc, _) | Row_async loc -> Some loc
  | Row_var n -> Some n.loc
  | Row_effect (path, _) ->
      Option.map (fun (n : name) -> n.loc) (List.nth_opt path 0)

(* A parameter's error: at [self] or at its name for what C can't pass, and at
   its type for one it can't take. *)
let param_error ~file (p : param) (h : Hir.param option) =
  match (p, h) with
  | Self_param (_, loc, _), _ ->
      Some (error ~file loc "a foreign function takes no receiver")
  | Param (Inout, name, _, _), _ ->
      Some (error ~file name.loc "C can't give back an `inout` parameter")
  | Param (_, name, _, true), _ ->
      Some (error ~file name.loc "C can't take an `escaping` parameter")
  | Param (Let, _, ty, false), Some (Param (_, _, t, _))
    when not (c_takes ~result:false t) ->
      Some
        (error ~file ty.loc
           "C can't take this type: use an integer, a float, `bool`, a `c.Ptr` \
            or a `c.Str`")
  | Param _, _ -> None

let signature ~file (f : fn_decl) (h : Hir.fn_decl option) =
  let generics =
    List.map
      (fun g ->
        error ~file (generic_loc g)
          "a foreign function takes no type, value or row parameter")
      f.generics
  in
  let hparams = match h with Some h -> h.params | None -> [] in
  let params =
    List.mapi (fun i p -> param_error ~file p (List.nth_opt hparams i)) f.params
    |> List.filter_map Fun.id
  in
  let result =
    match (f.ret, Option.bind h (fun h -> h.ret)) with
    | Some t, Some r when not (c_takes ~result:true r) ->
        [
          error ~file t.loc
            "C can't give this type: use an integer, a float, `bool`, a \
             `c.Ptr`, a `c.Str` or `()`";
        ]
    | _ -> []
  in
  let row =
    List.filter_map
      (fun e ->
        Option.map
          (fun l ->
            error ~file l
              "a foreign function may perform `io`, and no other effect")
          (row_loc e))
      f.row
  in
  generics @ params @ result @ row

(* The resolved declaration of the function [name] of the module of [file]. *)
let resolved (hir : Hir.program) file name =
  match List.find_opt (fun (m : Hir.module_) -> m.file = file) hir with
  | None -> None
  | Some m ->
      List.find_map
        (fun (d : Hir.decl Hir.node) ->
          match d.desc.kind with
          | Fn h when d.desc.foreign && h.name.desc = name -> Some h
          | _ -> None)
        m.decls

let check reads hir =
  List.concat_map
    (fun ((src : Program.source), tree) ->
      List.concat_map
        (fun (item : item) ->
          match item.desc with
          | Decl { foreign = true; kind = Fn f; _ } ->
              signature ~file:src.file f (resolved hir src.file f.name.desc)
          | _ -> [])
        tree.items)
    reads
