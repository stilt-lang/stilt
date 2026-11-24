type source = {
  module_path : string list;
  file : string;
  text : string;
  package : int;
}

type dep = {
  dep_name : string;
  target : int option;
  may_io : bool;
  may : Ast.capability list;
  may_unsafe : bool;
  key : Ast.loc;
}

type package = {
  name : string option;
  prefix : string option;
  manifest : string option;
  links : (string * Ast.loc) list;
  deps : dep list;
  declares : bool;
}

type packages = {
  list : package list;
  problems : Diagnostic.t list;
  root : string;
}

type t = { sources : source list; packages : packages }

let single =
  {
    list =
      [
        {
          name = None;
          prefix = None;
          manifest = None;
          links = [];
          deps = [];
          declares = true;
        };
      ];
    problems = [];
    root = ".";
  }

(* A file's text. A failure names the file, which a read of a directory's
   message doesn't. *)
let read path =
  try In_channel.with_open_bin path In_channel.input_all
  with Sys_error m when not (String.starts_with ~prefix:path m) ->
    raise (Sys_error (path ^ ": " ^ m))

let module_path file =
  String.split_on_char '/' (Filename.chop_suffix file ".lt")

(* Whether the directory [outer], a real path, is or holds the real path [d]. *)
let holds outer d =
  let prefix =
    if String.ends_with ~suffix:"/" outer then outer else outer ^ "/"
  in
  d = outer || String.starts_with ~prefix d

(* The modules' files below [Filename.concat dir relative], each with its
   path relative to [dir] (program.module-names): regular files whose names
   end in [.lt], found through symbolic links at the link's path, but for the
   entries whose names start with [.] and the links to a directory that is or
   holds one of [through], the real paths of the directories that the walk
   passes through. *)
let rec walk through dir relative =
  Sys.readdir (Filename.concat dir relative)
  |> Array.to_list
  |> List.filter (fun entry -> not (String.starts_with ~prefix:"." entry))
  |> List.concat_map (fun entry ->
      let path = if relative = "" then entry else relative ^ "/" ^ entry in
      let full = Filename.concat dir path in
      (* A link that names nothing, or a chain of links that never ends, names
         no file. *)
      match ((Unix.lstat full).st_kind, (Unix.stat full).st_kind) with
      | exception Unix.Unix_error _ -> []
      | own, Unix.S_DIR ->
          let real = Unix.realpath full in
          if own = Unix.S_LNK && List.exists (holds real) through then []
          else walk (real :: through) dir path
      | _, Unix.S_REG when Filename.check_suffix entry ".lt" -> [ path ]
      | _ -> [])

(* The modules' files below the module root [root]. *)
let files root = walk [ Unix.realpath root ] root ""

let by_file sources =
  List.sort (fun a b -> String.compare a.file b.file) sources

(* A module's name in the program, from its name in its package: in a
   dependency [D], its [main] is [D] and its [a.b] is [D.a.b] (packages.modules-of-dependencies). *)
let named prefix local =
  match (prefix, local) with
  | None, _ -> local
  | Some p, [ "main" ] -> [ p ]
  | Some p, _ -> p :: local

(* The modules below the module root [root], whose files are reported with
   [shown] before their paths from [root]. *)
let modules ~root ~shown ~package ~prefix =
  if not (Sys.file_exists root && Sys.is_directory root) then []
  else
    files root
    |> List.map (fun file ->
        {
          module_path = named prefix (module_path file);
          file = shown ^ file;
          text = read (Filename.concat root file);
          package;
        })

let local_path packages (src : source) =
  let prefix =
    Option.bind (List.nth_opt packages.list src.package) (fun p -> p.prefix)
  in
  match (prefix, src.module_path) with
  | Some p, [ first ] when first = p -> [ "main" ]
  | Some p, first :: rest when first = p -> rest
  | _ -> src.module_path

(* A root module named like a package that the root doesn't depend on would
   take its modules' names, so that package's modules take a prefix that no
   module can have. *)
let prefix_of (graph : Packages.t) root_sources i (p : Packages.package) =
  let name = Option.value p.manifest.name ~default:"" in
  let root = List.hd graph.packages in
  let direct =
    List.exists
      (fun (e : Manifest.entry) -> e.name = name)
      root.manifest.entries
  in
  let taken =
    List.exists (fun s -> List.hd s.module_path = name) root_sources
  in
  if i = 0 then None
  else if taken && not direct then Some (name ^ "~")
  else Some name

let package_of (p : Packages.package) prefix =
  let deps =
    List.map2
      (fun (e : Manifest.entry) target ->
        {
          dep_name = e.name;
          target;
          may_io = e.may_io;
          may = e.may;
          may_unsafe = e.may_unsafe;
          key = Packages.position p.text e.key_at;
        })
      p.manifest.entries p.deps
  in
  {
    name = p.manifest.name;
    prefix;
    manifest = Some (Packages.manifest_path p);
    links =
      List.map
        (fun (name, at) -> (name, Packages.position p.text at))
        p.manifest.links;
    deps;
    declares = p.manifest.declares;
  }

let load_package path =
  let graph = Packages.read_graph path in
  let src (p : Packages.package) = Filename.concat p.dir "src" in
  let root_sources =
    modules
      ~root:(src (List.hd graph.packages))
      ~shown:"src/" ~package:0 ~prefix:None
  in
  let prefixes = List.mapi (prefix_of graph root_sources) graph.packages in
  let sources =
    List.concat
      (List.mapi
         (fun i (p : Packages.package) ->
           if i = 0 then root_sources
           else
             modules ~root:(src p) ~shown:(p.shown ^ "/src/") ~package:i
               ~prefix:(List.nth prefixes i))
         graph.packages)
  in
  {
    sources = by_file sources;
    packages =
      {
        list = List.map2 package_of graph.packages prefixes;
        problems = graph.problems;
        root = path;
      };
  }

let load_libraries packages =
  let loaded = Hashtbl.create 4 in
  List.iter
    (fun p ->
      List.iter
        (fun (name, _) ->
          if not (Hashtbl.mem loaded name) then (
            Hashtbl.replace loaded name ();
            ignore (Foreign.load name)))
        p.links)
    packages.list

let load_found path =
  let inside name = Filename.concat path name in
  if not (Sys.file_exists path) then Error (path ^ " doesn't exist")
  else if not (Sys.is_directory path) then
    Ok
      {
        sources =
          [
            {
              module_path = [ "main" ];
              file = Filename.basename path;
              text = read path;
              package = 0;
            };
          ];
        packages = { single with root = Filename.dirname path };
      }
  else if Sys.file_exists (inside "stilt.toml") then
    try Ok (load_package path)
    with Packages.Fetched from ->
      Error
        ("a manifest names a fetched dependency, from " ^ from
       ^ ", and the reference interpreter reads path dependencies only")
  else if Sys.file_exists (inside "main.lt") then
    Ok
      {
        sources = by_file (modules ~root:path ~shown:"" ~package:0 ~prefix:None);
        packages = { single with root = path };
      }
  else Error (path ^ " is a directory without a main.lt, so not a program")

(* A file of the program that can't be read, as a dangling link, an
   unreadable file or a directory named [stilt.toml], makes the path no
   program, as a path that doesn't exist does. *)
let load path =
  try load_found path with Sys_error m -> Error ("cannot read " ^ m)

let examples = ref false
let read_std_examples () = examples := true
let reads_std_examples () = !examples

(* A doc example's line, cut to its [///]. *)
let without_examples text =
  let cut line =
    let rest = String.trim line in
    let is_example =
      String.starts_with ~prefix:"///" rest
      && String.starts_with ~prefix:"ex:"
           (String.trim (String.sub rest 3 (String.length rest - 3)))
    in
    if is_example then String.sub line 0 (String.index line '/') ^ "///"
    else line
  in
  String.concat "\n" (List.map cut (String.split_on_char '\n' text))

let std () =
  Std_files.files
  |> List.map (fun (file, text) ->
      let text = if !examples then text else without_examples text in
      {
        module_path = "std" :: module_path file;
        file = "std/" ^ file;
        text;
        package = 0;
      })
  |> by_file
