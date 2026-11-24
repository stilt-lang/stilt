(* Scale projects: directory programs of many modules that import one another,
   whose modules are csmith programs without [main]. *)

open Code
open Context
open Ty

(* A module of a scale project, as the modules that import it see it. Its
   items' names, and the names of the types in them, are qualified. *)
type exported = {
  name : string;  (** The name that [use] binds. *)
  path : string;  (** Its name, as [use] writes it. *)
  types : (string * decl) list;
  functions : fn_sig list;  (** Its [pub] functions. *)
  needs : string list;
      (** The modules that a module importing it must import too, so that it can
          name every type in these items: this module, and the modules whose
          types these items name, with what those need. *)
}

(* The module that declares the error type. Every other module imports it. *)
let errors = "errors"

(* [name] as other modules write it. A name without a qualifier is an item of
   the module being generated, [m]. *)
let qualify m name = if String.contains name '.' then name else m ^ "." ^ name
let home name = String.sub name 0 (String.index name '.')
let qualify_ty m = map_named (qualify m)

let qualify_decl m = function
  | Record fields ->
      Record (List.map (fun (f, t) -> (f, qualify_ty m t)) fields)
  | Variants cases ->
      Variants
        (List.map
           (fun (c, payload) -> (qualify m c, List.map (qualify_ty m) payload))
           cases)

let qualify_fn m f =
  {
    f with
    fname = qualify m f.fname;
    params = List.map (fun (inout, t) -> (inout, qualify_ty m t)) f.params;
    ret = qualify_ty m f.ret;
  }

(* The modules whose types the qualified items name. *)
let named_modules types functions =
  let decl_types = function
    | Record fields -> List.map snd fields
    | Variants cases -> List.concat_map snd cases
  in
  let fn_types f = f.ret :: List.map snd f.params in
  List.concat_map named
    (List.concat_map (fun (_, d) -> decl_types d) types
    @ List.concat_map fn_types functions)
  |> List.map home |> List.sort_uniq compare

(* What a module that imports [modules] can name: their types and [pub]
   functions, and the [use] declarations that import them, in the order they
   were generated. [before] is latest first. *)
let import p before modules =
  let imported =
    List.filter (fun m -> List.mem m.name modules) (List.rev before)
  in
  p.decls <- List.concat_map (fun m -> m.types) imported;
  p.fns <- List.concat_map (fun m -> m.functions) imported;
  line ("use " ^ errors)
  @ List.concat_map (fun m -> line ("use " ^ m.path)) imported

(* What a new module imports: a few of the modules before it, most of them
   recent, since code mostly uses its neighbours, with what those need. *)
let imports r before =
  if before = [] then []
  else
    let recent = List.filteri (fun i _ -> i < 16) before in
    Pick.times (Pick.between r 1 5) (fun () ->
        Pick.one r (if Pick.chance r 0.6 then recent else before))
    |> List.concat_map (fun m -> m.needs)
    |> List.sort_uniq compare

(* Module [index] of a scale project, and how its importers see it. Modules
   are grouped sixteen to a directory. *)
let scale_module p before index =
  let r = p.r in
  let name = "mod" ^ string_of_int index in
  let path = Printf.sprintf "part%d.%s" (index / 16) name in
  let uses = import p before (imports r before) in
  let types =
    Pick.times (Pick.between r 1 4) (fun () -> Csmith.type_decl p ~pub:true)
  in
  let functions =
    Pick.times (Pick.between r 3 10) (fun () ->
        let pub = Pick.chance r 0.7 in
        let f, lines = Csmith.function_ p ~budget:2_000 ~pub in
        (pub, f, lines))
  in
  let own_types =
    List.filter_map
      (fun (n, d) ->
        if String.contains n '.' then None
        else Some (qualify name n, qualify_decl name d))
      p.decls
  in
  let own_functions =
    List.filter_map
      (fun (pub, f, _) -> if pub then Some (qualify_fn name f) else None)
      functions
  in
  let needs =
    name
    :: List.concat_map
         (fun k ->
           if k = name then []
           else (List.find (fun m -> m.name = k) before).needs)
         (named_modules own_types own_functions)
    |> List.sort_uniq compare
  in
  ( { name; path; types = own_types; functions = own_functions; needs },
    (uses :: types) @ List.map (fun (_, _, lines) -> lines) functions )

(* A scale project from [seed], of at least [lines] lines: the module that
   declares the error type, modules that import one another in an acyclic
   graph, and [main], which imports the last eight of them. Each file comes
   with its path from the project's root. *)
let project ~seed ~lines =
  let p =
    {
      r = Pick.make seed;
      decls = [];
      fns = [];
      count = 0;
      fault = qualify errors fault;
      fault_variants =
        List.map
          (fun (c, payload) -> (qualify errors c, payload))
          fault_variants;
      panics = false;
    }
  in
  let file path items = (path, String.concat "\n" (List.map render items)) in
  let size (_, text) =
    String.fold_left (fun n c -> if c = '\n' then n + 1 else n) 0 text
  in
  let rec modules before files total =
    if total >= lines then (before, files)
    else
      let m, items = scale_module p before (List.length before) in
      let path = String.map (fun c -> if c = '.' then '/' else c) m.path in
      let f = file (path ^ ".lt") items in
      modules (m :: before) (f :: files) (total + size f)
  in
  let first = file (errors ^ ".lt") [ line ("pub " ^ fault_decl) ] in
  let before, files = modules [] [ first ] (size first) in
  let top = List.filteri (fun i _ -> i < 8) before in
  let uses =
    import p before
      (List.sort_uniq compare (List.concat_map (fun m -> m.needs) top))
  in
  List.rev (file "main.lt" [ uses; Csmith.main p ] :: files)
