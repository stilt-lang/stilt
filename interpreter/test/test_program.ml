(* Tests of how a program's files are found (program.forms and program.module-names). Each test
   writes a program to a fresh directory and prints the segments of each
   module's path, and its file. *)

open Stilt

let write dir (file, text) =
  let path = Filename.concat dir file in
  let rec make_parent path =
    let parent = Filename.dirname path in
    if not (Sys.file_exists parent) then (
      make_parent parent;
      Sys.mkdir parent 0o755)
  in
  make_parent path;
  Out_channel.with_open_bin path (fun oc -> output_string oc text)

let load ?(target = "") files =
  let dir = Filename.temp_dir "stilt" "program" in
  List.iter (write dir) files;
  match Program.load (Filename.concat dir target) with
  | Ok { sources; _ } ->
      List.iter
        (fun (s : Program.source) ->
          Printf.printf "[%s] %s\n" (String.concat ", " s.module_path) s.file)
        sources
  | Error _ -> print_endline "not a program"

let%expect_test "a single file is module main" =
  load ~target:"orders.lt" [ ("orders.lt", "") ];
  [%expect {| [main] orders.lt |}]

let%expect_test "a directory program" =
  load [ ("main.lt", ""); ("a/b.lt", ""); ("a.b.lt", ""); ("notes.txt", "") ];
  [%expect {|
    [a.b] a.b.lt
    [a, b] a/b.lt
    [main] main.lt
    |}]

let%expect_test "a package, which wins over main.lt" =
  load
    [
      ("stilt.toml", "");
      ("main.lt", "");
      ("src/main.lt", "");
      ("src/util/text.lt", "");
    ];
  [%expect {|
    [main] src/main.lt
    [util, text] src/util/text.lt
    |}]

let%expect_test "a package without src has no modules (program.forms)" =
  load [ ("stilt.toml", "not = [toml"); ("main.lt", "") ];
  [%expect {| |}]

let%expect_test "other directories aren't programs" =
  load [ ("lib.lt", "") ];
  [%expect {| not a program |}]

let%expect_test "a file that can't be read makes the path no program" =
  let dir = Filename.temp_dir "stilt" "program" in
  write dir ("main.lt", "fn main() {}\n");
  Sys.mkdir (Filename.concat dir "pkg") 0o755;
  Sys.mkdir (Filename.concat dir "pkg/stilt.toml") 0o755;
  let shown path =
    match Program.load path with
    | Ok _ -> print_endline "a program"
    | Error m ->
        let prefix = "cannot read " ^ dir ^ "/" in
        print_endline
          (String.sub m (String.length prefix)
             (String.length m - String.length prefix))
  in
  shown (Filename.concat dir "pkg");
  [%expect {| pkg/stilt.toml: Is a directory |}]

let%expect_test "entries whose names start with . are no part of the program" =
  load
    [
      ("main.lt", "");
      (".notes.lt", "");
      (".cache/x.lt", "");
      ("a/.b.lt", "");
      ("a/c.lt", "");
    ];
  [%expect {|
    [a, c] a/c.lt
    [main] main.lt
    |}]

(* Writes the program [files] and the links [links], each a target and the
   link's path, and prints its modules. *)
let linked files links =
  let dir = Filename.temp_dir "stilt" "program" in
  List.iter (write dir) files;
  List.iter
    (fun (target, path) -> Unix.symlink target (Filename.concat dir path))
    links;
  match Program.load dir with
  | Ok { sources; _ } ->
      List.iter
        (fun (s : Program.source) ->
          Printf.printf "[%s] %s\n" (String.concat ", " s.module_path) s.file)
        sources
  | Error m -> print_endline m

let%expect_test "modules are found through links, at the links' paths" =
  linked
    [ ("main.lt", ""); (".shared/util.lt", "") ]
    [
      (".shared", "lib");
      (".shared/util.lt", "tool.lt");
      ("missing.lt", "dangling.lt");
    ];
  [%expect
    {|
    [lib, util] lib/util.lt
    [main] main.lt
    [tool] tool.lt
    |}]

let%expect_test "a link that would make a cycle is skipped" =
  linked
    [ ("main.lt", ""); ("a/one.lt", ""); ("b/two.lt", "") ]
    [
      ("..", "a/up");
      ("../..", "far");
      ("../b", "a/x");
      ("../a", "b/y");
      ("itself", "itself");
    ];
  [%expect
    {|
    [a, one] a/one.lt
    [a, x, two] a/x/two.lt
    [b, two] b/two.lt
    [b, y, one] b/y/one.lt
    [main] main.lt
    |}]

let%expect_test "only regular files and links to them are modules" =
  let dir = Filename.temp_dir "stilt" "program" in
  write dir ("main.lt", "");
  Unix.mkfifo (Filename.concat dir "pipe.lt") 0o644;
  Unix.symlink "pipe.lt" (Filename.concat dir "piped.lt");
  Sys.mkdir (Filename.concat dir "folder.lt") 0o755;
  (match Program.load dir with
  | Ok { sources; _ } ->
      List.iter (fun (s : Program.source) -> print_endline s.file) sources
  | Error m -> print_endline m);
  [%expect {| main.lt |}]
