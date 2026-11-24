(* The directories, existence, removal and renaming of [std.fs] (std.directories). Each failure is classified as {!Files} classifies those of reading. *)

open Files

(* Runs [f], unless the path holds a NUL byte, which names no file. *)
let named path f =
  if String.contains path '\000' then Error Other
  else try f () with Unix.Unix_error (e, _, _) -> Error (error_of e)

let kind path =
  if String.contains path '\000' then None
  else try Some (Unix.stat path).st_kind with Unix.Unix_error _ -> None

let exists path = Option.is_some (kind path)
let is_file path = kind path = Some Unix.S_REG
let is_dir path = kind path = Some Unix.S_DIR

(* The names of a directory's entries, without [.] and [..]. *)
let entries path =
  let d = Unix.opendir path in
  Fun.protect ~finally:(fun () -> Unix.closedir d) @@ fun () ->
  let rec go acc =
    match Unix.readdir d with
    | "." | ".." -> go acc
    | name -> go (name :: acc)
    | exception End_of_file -> acc
  in
  go []

let list_dir path =
  named path @@ fun () ->
  if (Unix.stat path).st_kind <> S_DIR then Error Other
  else Ok (List.sort String.compare (List.map Strings.repair (entries path)))

let rec create_dir path =
  named path @@ fun () ->
  match Unix.stat path with
  | { st_kind = S_DIR; _ } -> Ok ()
  | _ -> Error Other
  | exception Unix.Unix_error (Unix.ENOENT, _, _) ->
      let parent = Filename.dirname path in
      let made = if parent = path then Ok () else create_dir parent in
      Result.bind made @@ fun () ->
      (* Another process may have made it meanwhile. *)
      (try Unix.mkdir path 0o777
       with Unix.Unix_error (Unix.EEXIST, _, _) when is_dir path -> ());
      Ok ()

let remove path =
  named path @@ fun () ->
  if (Unix.lstat path).st_kind = S_DIR then Unix.rmdir path
  else Unix.unlink path;
  Ok ()

(* [lstat] never follows a symbolic link, so a link is removed, not what it
   names. *)
let rec remove_tree path =
  if (Unix.lstat path).st_kind = S_DIR then (
    List.iter
      (fun name -> remove_tree (Filename.concat path name))
      (entries path);
    Unix.rmdir path)
  else Unix.unlink path

let remove_all path =
  named path @@ fun () ->
  remove_tree path;
  Ok ()

let rename from into =
  match named from (fun () -> Ok (ignore (Unix.lstat from))) with
  | Error e -> Error (e, from)
  | Ok () ->
      Result.map_error
        (fun e -> (e, into))
        (named into (fun () -> Ok (Unix.rename from into)))
