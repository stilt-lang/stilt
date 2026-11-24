(* The files that procedural macros' uses name (macros.named-files). *)

let dir (packages : Program.packages) (src : Program.source) =
  match List.nth_opt packages.list src.package with
  | Some { manifest = Some m; _ } ->
      Filename.concat packages.root (Filename.dirname m)
  | _ -> packages.root

let names path =
  let names = String.split_on_char '/' path in
  let bad name =
    name = "" || name = "." || name = ".."
    || String.starts_with ~prefix:"." name
  in
  if List.exists bad names then
    Error
      (Printf.sprintf
         "`%s` isn't a path a macro can be given: its names are separated by \
          `/`, and none is empty, `.` or `..`, or starts with `.`"
         path)
  else Ok names

(* Each name matches an entry of its directory byte for byte, whatever the
   file system's case. *)
let rec walk at = function
  | [] -> Ok at
  | name :: rest -> (
      match Sys.readdir at with
      | entries when Array.mem name entries ->
          walk (Filename.concat at name) rest
      | _ -> Error (Printf.sprintf "no entry of `%s` is named `%s`" at name)
      | exception Sys_error _ ->
          Error (Printf.sprintf "`%s` isn't a directory" at))

let inside dir file =
  match (Unix.realpath dir, Unix.realpath file) with
  | d, f -> String.starts_with ~prefix:(d ^ "/") f
  | exception Unix.Unix_error _ -> false

let read ~dir path =
  match Result.bind (names path) (walk dir) with
  | Error why -> Error why
  | Ok file -> (
      match Unix.stat file with
      | { st_kind = S_REG; _ } when inside dir file -> (
          match In_channel.with_open_bin file In_channel.input_all with
          | text when String.is_valid_utf_8 text -> Ok text
          | _ -> Error (Printf.sprintf "`%s` isn't UTF-8" path)
          | exception Sys_error _ ->
              Error (Printf.sprintf "`%s` can't be read" path))
      | { st_kind = S_REG; _ } ->
          Error
            (Printf.sprintf "`%s` lies outside the package's directory" path)
      | _ -> Error (Printf.sprintf "`%s` isn't a regular file" path)
      | exception Unix.Unix_error _ ->
          Error (Printf.sprintf "`%s` can't be read" path))
