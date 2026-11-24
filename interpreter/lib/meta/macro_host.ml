(* What a checked program tells of its procedural macros (macros.procedural-declarations and macros.step-limits). *)

let decls (hir : Hir.program) home =
  match List.find_opt (fun (m : Hir.module_) -> m.name = home) hir with
  | Some m -> (m.procs, m.decls)
  | None -> ([], [])

let fn_named decls name =
  List.find_map
    (fun (d : Hir.decl Hir.node) ->
      match d.desc.kind with
      | Fn f when f.name.desc = name -> Some f
      | _ -> None)
    decls

(* macros.procedural-declarations: the inputs and result of the macro [name] of [home]. *)
let state hir home name : Procs.state =
  let procs, decls = decls hir home in
  match fn_named decls name with
  | Some f when List.exists (fun (n : Hir.name) -> n.desc = name) procs -> (
      let inputs =
        List.map
          (function
            | Hir.Param (_, _, t, _) -> Procs.input t | Self_param _ -> None)
          f.params
      in
      match
        (Option.bind f.ret Procs.result, List.for_all Option.is_some inputs)
      with
      | Some result, true ->
          Usable { inputs = List.filter_map Fun.id inputs; result }
      | _ -> Unusable)
  | _ -> Unusable

(* macros.step-limits: the name of the function of [home] whose name is at [at]. *)
let named hir home (at : Ast.loc) =
  let _, decls = decls hir home in
  match
    List.find_map
      (fun (d : Hir.decl Hir.node) ->
        match d.desc.kind with
        | Fn f when f.name.loc = at -> Some f.name.desc
        | _ -> None)
      decls
  with
  | Some n -> n
  | None -> Printf.sprintf "the function at %d:%d" at.line at.col
