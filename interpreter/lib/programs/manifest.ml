(* A package's manifest, stilt.toml: its form and its keys (packages.manifest, packages.package-table and packages.dependencies; c.granting-unsafe and c.linking; editions.edition). Every error is an
   E0600, at the key or the value it is about. An entry with an error still
   declares its name (packages.manifests-with-errors). *)

type source =
  | Path of string
  | From of { from : string; version : string option; hash : string option }

type entry = {
  name : string;
  key_at : int;
  source : source option;
  may_io : bool;
  may : Ast.capability list;
  may_unsafe : bool;
}

type t = {
  name : string option;
  links : (string * int) list;
  declares : bool;
  entries : entry list;
  problems : (int * string) list;
}

let is_package_name s =
  Resolve_context.valid_module_path [ s ] && s <> "std" && s <> "main"

let is_path s = s <> "" && s.[0] <> '/' && not (String.contains s '\\')

let is_from s =
  match String.split_on_char '/' s with
  | _ when String.starts_with ~prefix:"file://" s ->
      let path = String.sub s 7 (String.length s - 7) in
      String.length path > 1 && path.[0] = '/'
  | authority :: (_ :: _ as segments) ->
      (* The host may give a port, as [HOST:PORT]. *)
      let host, port =
        match String.index_opt authority ':' with
        | Some i ->
            ( String.sub authority 0 i,
              String.sub authority (i + 1) (String.length authority - i - 1) )
        | None -> (authority, "0")
      in
      host <> ""
      && String.for_all
           (function
             | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '.' | '-' -> true
             | _ -> false)
           host
      && port <> ""
      && String.for_all (function '0' .. '9' -> true | _ -> false) port
      && List.for_all
           (fun seg ->
             seg <> ""
             && String.for_all
                  (fun c ->
                    not (List.mem c [ ' '; '\t'; '\n'; '\\'; '?'; '#' ]))
                  seg)
           segments
  | _ -> false

let is_version s =
  match String.split_on_char '.' s with
  | [ _; _; _ ] as parts ->
      List.for_all
        (fun p ->
          p <> ""
          && String.for_all (fun c -> c >= '0' && c <= '9') p
          && (String.length p = 1 || p.[0] <> '0')
          && Option.is_some (Int64.of_string_opt p))
        parts
  | _ -> false

let is_hash s =
  String.length s = 67
  && String.sub s 0 3 = "b3:"
  && String.for_all
       (function '0' .. '9' | 'a' .. 'f' -> true | _ -> false)
       (String.sub s 3 64)

type reader = { mutable problems : (int * string) list }

let problem r at message = r.problems <- (at, message) :: r.problems

let wrong r what wanted (v : Toml.value) =
  problem r v.at
    (Printf.sprintf "%s is %s, not %s" what wanted (Toml.describe v.kind))

(* A string of the form [ok], or [None] after its error. *)
let string_of r (v : Toml.value) what ok form =
  match v.kind with
  | String s when ok s -> Some s
  | String s ->
      problem r v.at (Printf.sprintf "`%s` isn't %s" s form);
      None
  | _ ->
      wrong r what "a string" v;
      None

(* One string of [may], given what the strings before it granted: [io], or
   capabilities, each once (packages.grants; facts.capability-grants), and [unsafe]
   once (c.granting-unsafe). *)
let rec grant r ((io, caps, unsafe) as granted) (e : Toml.value) =
  match e.kind with
  | String "unsafe" when unsafe ->
      problem r e.at "`unsafe` is granted twice";
      granted
  | String "unsafe" -> (io, caps, true)
  | _ ->
      let io, caps = grant_effect r (io, caps) e in
      (io, caps, unsafe)

and grant_effect r (io, caps) (e : Toml.value) =
  let twice what =
    problem r e.at (Printf.sprintf "`%s` is granted twice" what)
  in
  let with_io what =
    problem r e.at
      (Printf.sprintf
         "`io` grants every capability, so it isn't listed with `%s`" what)
  in
  match e.kind with
  | String "io" when io ->
      twice "io";
      (io, caps)
  | String "io" when caps <> [] ->
      with_io (Capability.name (List.hd caps));
      (io, caps)
  | String "io" -> (true, caps)
  | String s -> (
      match Capability.of_name s with
      | Some c when List.mem c caps ->
          twice s;
          (io, caps)
      | Some _ when io ->
          with_io s;
          (io, caps)
      | Some c -> (io, caps @ [ c ])
      | None ->
          problem r e.at
            (Printf.sprintf
               "`%s` isn't an effect, a capability or `unsafe`, which a \
                manifest grants: it grants `io`, capabilities among %s, and \
                `unsafe`"
               s
               (String.concat ", "
                  (List.map
                     (fun c -> "`" ^ Capability.name c ^ "`")
                     Capability.all)));
          (io, caps))
  | _ ->
      wrong r "an effect" "a string" e;
      (io, caps)

(* [may], a list of the effects and capabilities granted. *)
let may r (v : Toml.value) =
  match v.kind with
  | Array effects -> List.fold_left (grant r) (false, [], false) effects
  | _ ->
      wrong r "`may`" "a list of strings" v;
      (false, [], false)

let combination ~path ~from ~version ~hash =
  match (path, from) with
  | Some _, Some _ -> Error "has both `path` and `from`"
  | None, None -> Error "has neither `path` nor `from`"
  | Some _, None when version <> None -> Error "has a `version`"
  | Some _, None when hash <> None -> Error "has a `hash`"
  | Some p, None -> Ok (Path p)
  | None, Some _ when hash <> None && version = None ->
      Error "has a `hash` without its `version`"
  | None, Some f -> Ok (From { from = f; version; hash })

let entry r name key_at (fields : Toml.table) =
  let before = List.length r.problems in
  let path = ref None and from = ref None and version = ref None in
  let hash = ref None and io = ref (false, [], false) in
  List.iter
    (fun (e : Toml.entry) ->
      let v = e.value in
      match e.key with
      | "path" -> path := string_of r v "`path`" is_path "a relative path"
      | "from" -> from := string_of r v "`from`" is_from "a git repository"
      | "version" -> version := string_of r v "`version`" is_version "a version"
      | "hash" -> hash := string_of r v "`hash`" is_hash "a content hash"
      | "may" -> io := may r v
      | other ->
          problem r e.key_at
            (Printf.sprintf "a dependency's entry has no key `%s`" other))
    fields.entries;
  let source =
    if List.length r.problems > before then None
    else
      match
        combination ~path:!path ~from:!from ~version:!version ~hash:!hash
      with
      | Ok s -> Some s
      | Error why ->
          problem r key_at (Printf.sprintf "the entry `%s` %s" name why);
          None
  in
  let may_io, may, may_unsafe = !io in
  { name; key_at; source; may_io; may; may_unsafe }

(* c.finding-libraries: a library's name, of letters, digits, [_], [-] and [.]. *)
let is_library s =
  s <> ""
  && String.for_all
       (function
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' -> true
         | _ -> false)
       s

(* [link], the C libraries the package's foreign functions need. *)
let link r (v : Toml.value) =
  match v.kind with
  | Array names ->
      List.filter_map
        (fun (n : Toml.value) ->
          Option.map
            (fun s -> (s, n.at))
            (string_of r n "a library" is_library
               "a library's name, of letters, digits, `_`, `-` and `.`"))
        names
  | _ ->
      wrong r "`link`" "a list of strings" v;
      []

let package r (name, links) (v : Toml.value) =
  match v.kind with
  | Table t ->
      List.iter
        (fun (e : Toml.entry) ->
          match (e.key, e.value.kind) with
          | "name", String s when is_package_name s -> name := Some s
          | "name", String s ->
              problem r e.value.at
                (Printf.sprintf "`%s` isn't a valid package name" s)
          | "name", _ -> wrong r "a package's name" "a string" e.value
          (* editions.edition: the editions are 2027 alone. *)
          | "edition", String "2027" -> ()
          | "edition", String s ->
              problem r e.value.at
                (Printf.sprintf
                   "this manifest's edition is `%s`, and the editions are 2027"
                   s)
          | "edition", _ -> wrong r "a package's edition" "a string" e.value
          | "link", _ -> links := link r e.value
          | key, _ ->
              problem r e.key_at
                (Printf.sprintf "`[package]` has no key `%s`" key))
        t.entries
  | _ -> wrong r "`[package]`" "a table" v

let dependencies r (t : Toml.table) =
  List.map
    (fun (e : Toml.entry) ->
      match e.value.kind with
      | Table fields -> entry r e.key e.key_at fields
      | _ ->
          wrong r (Printf.sprintf "the entry `%s`" e.key) "a table" e.value;
          {
            name = e.key;
            key_at = e.key_at;
            source = None;
            may_io = false;
            may = [];
            may_unsafe = false;
          })
    t.entries

let read text =
  match Toml.parse text with
  | Error (at, why) ->
      {
        name = None;
        links = [];
        declares = false;
        entries = [];
        problems = [ (at, "this manifest isn't TOML 1.0: " ^ why) ];
      }
  | Ok root ->
      let r = { problems = [] } in
      let name = ref None and declares = ref true and entries = ref [] in
      let links = ref [] in
      List.iter
        (fun (e : Toml.entry) ->
          match (e.key, e.value.kind) with
          | "package", _ -> package r (name, links) e.value
          | "dependencies", Table t -> entries := dependencies r t
          | "dependencies", _ ->
              declares := false;
              wrong r "`[dependencies]`" "a table" e.value
          | key, (Table _ | Tables _) ->
              problem r e.key_at
                (Printf.sprintf "a manifest has no table `%s`" key)
          | key, _ ->
              problem r e.key_at
                (Printf.sprintf "a manifest has no key `%s`" key))
        root.entries;
      {
        name = !name;
        links = !links;
        declares = !declares;
        entries = !entries;
        problems = List.rev r.problems;
      }
