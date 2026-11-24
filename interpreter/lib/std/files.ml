type error = Missing | Denied | Invalid_utf8 | Other

let error_of = function
  | Unix.ENOENT | Unix.ENOTDIR -> Missing
  | Unix.EACCES | Unix.EPERM -> Denied
  | _ -> Other

(* Runs [f] on a file opened with [flags], unless opening it fails. A path
   that holds a NUL byte names no file a program could mean, so it fails
   without being looked up. *)
let with_file path flags f =
  if String.contains path '\000' then Error Other
  else
    match Unix.openfile path flags 0o666 with
    | exception Unix.Unix_error (e, _, _) -> Error (error_of e)
    | fd ->
        Fun.protect ~finally:(fun () -> Unix.close fd) @@ fun () ->
        if (Unix.fstat fd).st_kind = S_DIR then Error Other else f fd

(* The bytes of a file, whatever they are. *)
let read_bytes path =
  with_file path [ O_RDONLY ] @@ fun fd ->
  let b = Buffer.create 4096 and chunk = Bytes.create 65536 in
  let rec go () =
    match Unix.read fd chunk 0 (Bytes.length chunk) with
    | 0 -> Ok (Buffer.contents b)
    | n ->
        Buffer.add_subbytes b chunk 0 n;
        go ()
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> go ()
    | exception Unix.Unix_error (e, _, _) -> Error (error_of e)
  in
  go ()

let read path =
  Result.bind (read_bytes path) (fun text ->
      if String.is_valid_utf_8 text then Ok text else Error Invalid_utf8)

(* Writes [text] to a file opened with [flags]. *)
let write_with flags path text =
  with_file path flags @@ fun fd ->
  let rec go offset =
    if offset = String.length text then Ok ()
    else
      match
        Unix.write_substring fd text offset (String.length text - offset)
      with
      | n -> go (offset + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go offset
      | exception Unix.Unix_error (e, _, _) -> Error (error_of e)
  in
  go 0

let write = write_with [ O_WRONLY; O_CREAT; O_TRUNC ]
let append = write_with [ O_WRONLY; O_CREAT; O_APPEND ]
