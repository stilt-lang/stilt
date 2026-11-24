(* The packages of a program: the root package, and those that its manifest
   names through path entries, directly or through the manifests of the
   packages it names (packages.path-dependencies, packages.one-name-one-package and packages.dependency-cycles). Each entry of the root's
   manifest brings the packages that it reaches through entries without errors,
   unless they hold a cycle (E0609) or a second package of a name already in
   the program (E0606): then it brings none, and its name stands for nothing
   (packages.manifests-with-errors). Packages that only such an entry reaches aren't part of the
   program, and none of their diagnostics is reported. *)

exception Fetched of string

type package = {
  dir : string;
  shown : string;
  manifest : Manifest.t;
  text : string;
  mutable deps : int option list;
}

type walk = {
  loaded : package Dynarray.t;
  by_dir : (string, int) Hashtbl.t;
  resolved : (int * int, int option) Hashtbl.t;
  mutable problems : (int * Diagnostic.t) list;
}

let read path =
  try In_channel.with_open_bin path In_channel.input_all
  with Sys_error m when not (String.starts_with ~prefix:path m) ->
    raise (Sys_error (path ^ ": " ^ m))

let identity dir = try Unix.realpath dir with Unix.Unix_error _ -> dir

let manifest_path p =
  if p.shown = "" then "stilt.toml" else p.shown ^ "/stilt.toml"

(* The line and column of a byte offset, counting Unicode scalar values. *)
let position text offset =
  let line = ref 1 and col = ref 1 and i = ref 0 in
  while !i < offset && !i < String.length text do
    let d = String.get_utf_8_uchar text !i in
    if text.[!i] = '\n' then (
      incr line;
      col := 1)
    else incr col;
    i := !i + max 1 (Uchar.utf_decode_length d)
  done;
  { Ast.line = !line; col = !col }

let diagnostic p code offset message =
  Diagnostic.at ~file:(manifest_path p) code (position p.text offset) message

(* A relative path with its [.] and [..] segments resolved, but for those that
   climb above the root. *)
let normalized path =
  let parts =
    List.fold_left
      (fun acc seg ->
        match (seg, acc) with
        | ("" | "."), _ -> acc
        | "..", last :: rest when last <> ".." -> rest
        | _ -> seg :: acc)
      []
      (String.split_on_char '/' path)
  in
  String.concat "/" (List.rev parts)

let add w dir shown =
  let file = Filename.concat dir "stilt.toml" in
  if not (Sys.file_exists file) then None
  else
    let text = read file in
    let p = { dir; shown; manifest = Manifest.read text; text; deps = [] } in
    let index = Dynarray.length w.loaded in
    List.iter
      (fun (at, m) ->
        w.problems <- (index, diagnostic p Code.e0600 at m) :: w.problems)
      p.manifest.problems;
    (* c.finding-libraries: each library, as the dynamic loader finds it. *)
    List.iter
      (fun (name, at) ->
        if not (Foreign.load name) then
          let message =
            Printf.sprintf
              "the C library `%s` isn't found: no lib%s on the system's paths"
              name name
          in
          w.problems <-
            (index, diagnostic p Code.e0611 at message) :: w.problems)
      p.manifest.links;
    Hashtbl.replace w.by_dir (identity dir) index;
    Dynarray.add_last w.loaded p;
    Some index

(* The target of an entry, when its manifest names its package as the entry
   does (packages.dependency-names). *)
let named w index (e : Manifest.entry) target =
  let p = Dynarray.get w.loaded index and t = Dynarray.get w.loaded target in
  match t.manifest.name with
  | Some n when n = e.name -> Some target
  | found ->
      let message =
        match found with
        | Some n ->
            Printf.sprintf
              "this entry names `%s`, but %s names its package `%s`" e.name
              (manifest_path t) n
        | None ->
            Printf.sprintf
              "this entry names `%s`, but %s gives its package no name" e.name
              (manifest_path t)
      in
      w.problems <-
        (index, diagnostic p Code.e0603 e.key_at message) :: w.problems;
      None

let resolve w index e =
  let p = Dynarray.get w.loaded index in
  let entry = List.nth p.manifest.entries e in
  match entry.source with
  | None -> None
  | Some (From { from; _ }) -> raise (Fetched from)
  | Some (Path path) -> (
      let dir = Filename.concat p.dir path in
      let shown =
        normalized (if p.shown = "" then path else p.shown ^ "/" ^ path)
      in
      match Hashtbl.find_opt w.by_dir (identity dir) with
      | Some known -> named w index entry known
      | None -> (
          match add w dir shown with
          | Some target -> named w index entry target
          | None ->
              let message =
                Printf.sprintf "`%s` names %s, which holds no stilt.toml"
                  entry.name shown
              in
              w.problems <-
                (index, diagnostic p Code.e0601 entry.key_at message)
                :: w.problems;
              None))

let target w index e =
  match Hashtbl.find_opt w.resolved (index, e) with
  | Some found -> found
  | None ->
      let found = resolve w index e in
      Hashtbl.replace w.resolved (index, e) found;
      found

(* The packages that [start] reaches, and whether one depends on itself or on
   the root. *)
let closure w start =
  let members = ref [] and cycle = ref false in
  let rec visit stack node =
    if List.mem node stack then cycle := true
    else if not (List.mem node !members) then (
      members := node :: !members;
      let p = Dynarray.get w.loaded node in
      List.iteri
        (fun e _ -> Option.iter (visit (node :: stack)) (target w node e))
        p.manifest.entries)
  in
  visit [ 0 ] start;
  (List.rev !members, !cycle)

(* The message of two packages of one name, if [members] brings one. *)
let clash w included members =
  let seen = Hashtbl.create 8 in
  List.find_map
    (fun m ->
      let p = Dynarray.get w.loaded m in
      match p.manifest.name with
      | None -> None
      | Some name -> (
          match Hashtbl.find_opt seen name with
          | Some other when other <> m ->
              Some
                (Printf.sprintf "this entry brings a second package `%s`" name)
          | _ ->
              Hashtbl.replace seen name m;
              None))
    (included @ members)

type t = { packages : package list; problems : Diagnostic.t list }

let report w index code offset message =
  let p = Dynarray.get w.loaded index in
  w.problems <- (index, diagnostic p code offset message) :: w.problems

(* Brings the packages of entry [e] of the root's manifest into [included], or
   reports why it can't. *)
let bring w included e (entry : Manifest.entry) =
  match target w 0 e with
  | None -> included
  | Some t -> (
      let members, cycle = closure w t in
      let broken code message =
        report w 0 code entry.key_at message;
        Hashtbl.replace w.resolved (0, e) None;
        included
      in
      if cycle then
        let name =
          Option.value (Dynarray.get w.loaded t).manifest.name ~default:""
        in
        broken Code.e0609
          (Printf.sprintf
             "`%s` depends on itself, through the manifests of its dependencies"
             name)
      else
        match clash w included members with
        | Some message -> broken Code.e0606 message
        | None ->
            included @ List.filter (fun m -> not (List.mem m included)) members)

let read_graph root =
  let w =
    {
      loaded = Dynarray.create ();
      by_dir = Hashtbl.create 8;
      resolved = Hashtbl.create 8;
      problems = [];
    }
  in
  ignore (add w root "");
  let entries = (Dynarray.get w.loaded 0).manifest.entries in
  let included = ref [ 0 ] in
  List.iteri (fun e entry -> included := bring w !included e entry) entries;
  let index = Hashtbl.create 8 in
  List.iteri (fun i l -> Hashtbl.replace index l i) !included;
  let package l =
    let p = Dynarray.get w.loaded l in
    p.deps <-
      List.mapi
        (fun e _ ->
          match Hashtbl.find_opt w.resolved (l, e) with
          | Some (Some t) -> Hashtbl.find_opt index t
          | _ -> None)
        p.manifest.entries;
    p
  in
  {
    packages = List.map package !included;
    problems =
      List.filter_map
        (fun (l, d) -> if Hashtbl.mem index l then Some d else None)
        (List.rev w.problems);
  }
