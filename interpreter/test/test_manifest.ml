(* Tests of manifests (packages.manifest, packages.package-table and packages.manifest-diagnostics): where TOML stops being
   TOML 1.0, and the E0600s of a manifest's keys and values, each printed as the
   text it is at. The compiler's tests in stilt-pkg check the same places. *)

open Stilt

let verdict text =
  match Toml.parse text with
  | Ok _ -> print_endline "ok"
  | Error (at, _) ->
      let loc = Packages.position text at in
      Printf.printf "%d:%d\n" loc.line loc.col

let%expect_test "syntax errors are where no document can continue" =
  List.iter verdict
    [
      "this is [not toml";
      "[dependencies]\njson = { path = \"deps/json\" # no\n";
      "a = \"open\n";
      "a = \"\\q\"";
      "a = 01";
      "a = 1__2";
      "a = 1.";
      "a = { b = 1, }";
      "a = { b = 1,\n c = 2 }";
      "a = tru";
      "a = yes";
      "[a";
      "a = 1979-13-01";
      "a = \"\"\"x\"\"\"\"\"\"";
      "a = 1\r";
      "a = 1 2";
    ];
  [%expect
    {|
    1:6
    2:29
    1:10
    1:7
    1:6
    1:7
    1:7
    1:14
    1:13
    1:8
    1:5
    1:3
    1:10
    1:14
    1:6
    1:7
    |}]

let%expect_test "redefinitions are at their keys" =
  List.iter verdict
    [
      "a = 1\na = 2";
      "[a]\n[a]";
      "[a]\nb.c = 1\n[a.b]";
      "[a.b]\nc = 1\n[a]\nb.d = 2";
      "a = { b = 1 }\n[a]";
      "a = [1]\n[[a]]";
      "a = { b = 1, b = 2 }";
      "[a.b.c]\n[a]\nb.d = 1";
      "a.b = 1\n[a.c]";
      "# a comment\n\
       t = 'x' # after\n\
       d = 1979-05-27T07:32:00.999-07:00\n\
       l = [\n\
      \  1, # one\n\
      \  \"two\",\n\
       ]\n\
       m = \"\"\"\n\
       one \\\n\
      \  two\"\"\"\n\
       [[f]]\n\
       n = 1\n\
       [[f]]\n\
       n = 2\n";
    ];
  [%expect
    {|
    2:1
    2:2
    3:2
    4:1
    2:2
    2:3
    1:14
    ok
    ok
    ok
    |}]

let%expect_test "a manifest's errors are at the keys and values they are about"
    =
  let text =
    "edition = \"2024\"\n\
     [package]\n\
     name = \"Json\"\n\
     version = \"1.0.0\"\n\
     [dependencies]\n\
     a = \"deps/a\"\n\
     b = { path = [\"deps\"] }\n\
     c = { path = \"deps/c\", features = [] }\n\
     d = { path = \"deps/d\", from = \"github.com/x/d\" }\n\
     e = { may = [\"io\"] }\n\
     f = { from = \"github.com/x/f\", version = \"1.04.0\" }\n\
     g = { path = \"deps/g\", may = [\"net\", \"io\", \"io\"] }\n\
     h = { from = \"github.com/x/h\", hash = \"b3:00\" }\n"
  in
  let m = Manifest.read text in
  List.iter
    (fun (at, _) ->
      let loc = Packages.position text at in
      Printf.printf "%d:%d\n" loc.line loc.col)
    m.problems;
  (* [net] is a capability, so on line 12 the first [io] is listed with a
     capability, and the second is too (facts.capability-grants). *)
  [%expect
    {|
    1:1
    3:8
    4:1
    6:5
    7:14
    8:24
    9:1
    10:1
    11:42
    12:38
    12:44
    13:39
    |}]

(* facts.capability-grants *)
let%expect_test "may grants io or capabilities, each once" =
  let grants may =
    let m =
      Manifest.read
        ("[dependencies]\nd = { path = \"deps/d\", may = [" ^ may ^ "] }\n")
    in
    List.iter
      (fun (e : Manifest.entry) ->
        Printf.printf "io=%b [%s]" e.may_io
          (String.concat " " (List.map Capability.name e.may)))
      m.entries;
    List.iter (fun (_, why) -> Printf.printf " E0600: %s" why) m.problems;
    print_newline ()
  in
  grants {|"io"|};
  grants {|"console", "fs"|};
  grants {|"files"|};
  grants {|"fs", "fs"|};
  grants {|"io", "fs"|};
  grants {|"spawn", "io"|};
  [%expect
    {|
    io=true []
    io=false [console fs]
    io=false [] E0600: `files` isn't an effect, a capability or `unsafe`, which a manifest grants: it grants `io`, capabilities among `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn`, `exec`, and `unsafe`
    io=false [fs] E0600: `fs` is granted twice
    io=true [] E0600: `io` grants every capability, so it isn't listed with `fs`
    io=false [spawn] E0600: `io` grants every capability, so it isn't listed with `spawn`
    |}]

(* packages.dependencies: the forms of an entry's values, each accepted or an E0600. *)
let%expect_test "an entry's values have the forms the table gives" =
  let accepted entry =
    let m = Manifest.read ("[dependencies]\nd = { " ^ entry ^ " }\n") in
    Printf.printf "%b " (m.problems = [])
  in
  let hash = "b3:" ^ String.make 64 'a' in
  List.iter accepted
    [
      {|path = "deps/d"|};
      {|path = ""|};
      {|path = "/abs/d"|};
      {|path = "deps\\d"|};
      {|from = "github.com/x/d"|};
      {|from = "git.example.org:8443/x/d"|};
      {|from = "github.com"|};
      {|from = "/x/d"|};
      {|from = "github.com:/x/d"|};
      {|from = "github.com:84a/x/d"|};
      {|from = "git_hub.com/x/d"|};
      {|from = "file:///repos/d"|};
      {|from = "file://repos/d"|};
    ];
  print_newline ();
  List.iter accepted
    [
      {|from = "github.com/x/d", version = "1.0.0"|};
      {|from = "github.com/x/d", version = "0.10.200"|};
      {|from = "github.com/x/d", version = "1.04.0"|};
      {|from = "github.com/x/d", version = "1.0"|};
      {|from = "github.com/x/d", version = "1..0"|};
      {|from = "github.com/x/d", version = "1.0.a"|};
      {|from = "github.com/x/d", version = "9.19.0"|};
      Printf.sprintf {|from = "github.com/x/d", version = "1.0.0", hash = "%s"|}
        hash;
      Printf.sprintf {|from = "github.com/x/d", version = "1.0.0", hash = "%s"|}
        (String.uppercase_ascii hash);
      Printf.sprintf
        {|from = "github.com/x/d", version = "1.0.0", hash = "%s0"|} hash;
      Printf.sprintf
        {|from = "github.com/x/d", version = "1.0.0", hash = "b3:%sg"|}
        (String.make 63 'a');
      Printf.sprintf
        {|from = "github.com/x/d", version = "1.0.0", hash = "b4:%s"|}
        (String.make 64 'a');
    ];
  [%expect
    {|
    true false false false true true false false false false false true false
    true true false false false false true true false false false false
    |}]
