(* Tests of reading and writing files (std.fs). Each test works in a
   fresh directory and prints what each operation gives. *)

open Stilt

let show = function
  | Ok text -> Printf.printf "Ok %S\n" text
  | Error (error : Files.error) ->
      print_endline
        (match error with
        | Missing -> "NotFound"
        | Denied -> "PermissionDenied"
        | Invalid_utf8 -> "InvalidUtf8"
        | Other -> "Other")

let in_fresh_dir f = f (Filename.temp_dir "stilt" "files")

let%expect_test "reading and writing" =
  in_fresh_dir @@ fun dir ->
  let path = Filename.concat dir "notes.txt" in
  show (Result.map (fun () -> "written") (Files.write path "hé\r\n"));
  show (Files.read path);
  show (Result.map (fun () -> "replaced") (Files.write path ""));
  show (Files.read path);
  [%expect
    {|
    Ok "written"
    Ok "h\195\169\r\n"
    Ok "replaced"
    Ok ""
    |}]

let%expect_test "each kind of failure" =
  in_fresh_dir @@ fun dir ->
  let file = Filename.concat dir "notes.txt" in
  ignore (Files.write file "x");
  let bad = Filename.concat dir "bad.txt" in
  Out_channel.with_open_bin bad (fun oc -> output_string oc "\xff");
  (* A missing file, a missing directory, a path through a file, a directory,
     a path holding NUL, and bytes that aren't UTF-8. *)
  List.iter
    (fun path -> show (Files.read path))
    [
      Filename.concat dir "absent.txt";
      Filename.concat dir "absent/notes.txt";
      Filename.concat file "x";
      dir;
      file ^ "\000.txt";
      bad;
    ];
  show
    (Result.map
       (fun () -> "")
       (Files.write (Filename.concat dir "absent/x") ""));
  show (Result.map (fun () -> "") (Files.write dir ""));
  [%expect
    {|
    NotFound
    NotFound
    NotFound
    Other
    Other
    InvalidUtf8
    NotFound
    Other
    |}]
