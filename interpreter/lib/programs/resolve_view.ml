(* What the [use] declarations of a package's modules can name (packages.modules-of-dependencies, packages.imports and packages.manifests-with-errors): the package's own modules, by their names in it; [std]; and the
   packages its manifest names as dependencies, by their names. A path is
   translated once into the name of a namespace of the program, so that what
   follows a [use] reads the program's names. *)

open Resolve_context
open Resolve_scopes

let join prefix rest = if rest = "" then prefix else prefix ^ "." ^ rest

let split written =
  match String.index_opt written '.' with
  | Some i ->
      ( String.sub written 0 i,
        String.sub written (i + 1) (String.length written - i - 1) )
  | None -> (written, "")

(* The name in the program of [local], a namespace of a package's own
   modules. *)
let in_program prefix local =
  match prefix with
  | None -> local
  | Some p when local = "main" -> p
  | Some p -> join p local

let prefix_of (packages : Program.packages) i =
  Option.value ~default:""
    (Option.bind (List.nth_opt packages.list i) (fun (p : Program.package) ->
         p.prefix))

(* A module of another package of the program that isn't a dependency (E0218):
   not the root's, whose modules keep their names. *)
let foreign (packages : Program.packages) env package (p : Program.package)
    first rest =
  let named i (q : Program.package) =
    i <> 0 && i <> package && q.name = Some first
    && not (List.exists (fun (d : Program.dep) -> d.dep_name = first) p.deps)
  in
  let found = ref false in
  List.iteri
    (fun i q ->
      if named i q && Sset.mem (join (prefix_of packages i) rest) env.namespaces
      then found := true)
    packages.list;
  if !found then Foreign first else Missing

let own (packages : Program.packages) units env package (p : Program.package)
    written =
  let first, rest = split written in
  let mine =
    List.filter (fun u -> (not u.std) && u.source.package = package) units
  in
  let under l = l = written || String.starts_with ~prefix:(written ^ ".") l in
  if List.exists (fun u -> u.valid && under u.local) mine then
    Found (in_program p.prefix written)
  else if List.exists (fun u -> (not u.valid) && under u.local) mine then
    Unnamed
  else if not p.declares then Unnamed
  else foreign packages env package p first rest

let view (packages : Program.packages) units env package written =
  match List.nth_opt packages.list package with
  | None | Some { manifest = None; _ } -> whole_view env written
  | Some p -> (
      let first, rest = split written in
      if first = "std" then whole_view env written
      else
        match
          List.find_opt (fun (d : Program.dep) -> d.dep_name = first) p.deps
        with
        | Some { target = None; _ } -> Unnamed
        | Some { target = Some t; _ } ->
            whole_view env (join (prefix_of packages t) rest)
        | None -> own packages units env package p written)
