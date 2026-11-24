(* Tests of name resolution against the rules on modules (program.module-names, program.module-header and program.visibility): their names, headers, imports, dependencies and private items, and a
   syntax error in one of them, which comes alone (errors.syntax-errors). Most tests
   print a program's diagnostics as conformance.diagnostic-lines compares them: a file, a line and a
   code. *)

open Diagnostics
open Resolved

(* program.module-names *)
let%expect_test "module names are lowercase identifiers outside std" =
  check
    [
      ("main.lt", "");
      ("Upper.lt", "");
      ("my-module.lt", "");
      ("a.b.lt", "");
      ("a/type.lt", "");
      ("a/str.lt", "");
      ("std/extra.lt", "");
      ("_private.lt", "");
      ("a/b_2.lt", "");
    ];
  [%expect
    {|
    Upper.lt:1: E0200
    a.b.lt:1: E0200
    a/str.lt:1: E0200
    a/type.lt:1: E0200
    my-module.lt:1: E0200
    std/extra.lt:1: E0200
    |}]

let%expect_test "a module with an invalid name is checked on its own" =
  (* Its scope is its own, even when its name is that of a std module. *)
  check
    [
      ("main.lt", ""); ("std/prelude.lt", "fn f() { g() }\nfn g() {}\nfn g() {}");
    ];
  [%expect {|
    std/prelude.lt:1: E0200
    std/prelude.lt:3: E0208
    |}];
  (* Naming it is no further error. *)
  check
    [
      ("main.lt", "use str\nuse util\nfn f() { util.Text.g() }");
      ("str.lt", "");
      ("util/Text.lt", "pub fn g() {}");
    ];
  [%expect {|
    str.lt:1: E0200
    util/Text.lt:1: E0200
    |}]

(* program.header-limits *)
let%expect_test "headers match the module and name each limit once" =
  main "module main\nwithout panic, alloc";
  [%expect {| ok |}];
  main "module orders";
  [%expect {| main.lt:1: E0201 |}];
  check [ ("main.lt", ""); ("a/b.lt", "module a.c") ];
  [%expect {| a/b.lt:1: E0201 |}];
  main "module main\nwithout alloc,\n  panic,\n  alloc";
  [%expect {| main.lt:4: E0202 |}];
  (* A second clause is reported at its [without], and its limits are
     ignored: the repeated [panic] in it is no further error, and the index
     isn't limited. *)
  main
    "module main\n\
     without alloc\n\
     without panic, panic\n\
     fn f(xs: List<i64>) -> i64 { xs[0] }";
  [%expect {| main.lt:3: E0202 |}]

(* declarations.limits *)
let%expect_test "a function's clause names panic and alloc, each once" =
  main "fn f() without panic, alloc {}";
  [%expect {| ok |}];
  main "fn f() without alloc,\n  alloc {}";
  [%expect {| main.lt:2: E0202 |}];
  main "trait T { fn t(self) -> i64 without panic, panic { 1 } }";
  [%expect {| main.lt:1: E0202 |}]

(* facts.spelling *)
let%expect_test "div and copy are named once each" =
  main "module main\nwithout div, copy\nfn f() without copy, div {}";
  [%expect {| ok |}];
  main "fn f() without div, copy,\n  div {}";
  [%expect {| main.lt:2: E0202 |}];
  main "module main\nwithout copy, panic,\n  copy";
  [%expect {| main.lt:3: E0202 |}]

(* program.what-use-binds *)
let%expect_test "use imports modules and namespaces" =
  main "use std.fs\nfn f() { let _ = fs.read }";
  [%expect {| ok |}];
  main "use std\nfn f() { let _ = std.fs.read }";
  [%expect {| ok |}];
  main "use std.nothing\nuse std.fs.read\nfn f() { nothing.g() }";
  [%expect {|
    main.lt:1: E0205
    main.lt:2: E0230
    |}];
  (* A [use] that names an item, by its last name or one before, binds its
     name to the error type; a path that names no item of a module is
     E0205. *)
  main
    "use std.sync.Shared\n\
     use std.sync.Shared.new\n\
     use std.io.nothing\n\
     fn f(h: Shared<i64>) -> Shared<i64> { h }";
  [%expect
    {|
    main.lt:1: E0230
    main.lt:2: E0230
    main.lt:3: E0205
    |}];
  check
    [
      ("main.lt", "use a\nfn f() { a.b.c.g() }");
      ("a.lt", "");
      ("a/b/c.lt", "pub fn g() {}");
    ];
  [%expect {| ok |}];
  check [ ("main.lt", "use a.b\nuse x.b"); ("a/b.lt", ""); ("x/b.lt", "") ];
  [%expect {| main.lt:2: E0208 |}];
  check [ ("main.lt", "use a\nuse x.b"); ("a/b.lt", ""); ("x/b.lt", "") ];
  [%expect {| ok |}];
  (* A clash is reported at the later declaration, wherever its name is. *)
  main "use std.io\nuse std\n  .io";
  [%expect {| main.lt:2: E0208 |}]

let%expect_test "an item hides a child module of the same name" =
  let files main =
    [
      ("main.lt", "use a\n" ^ main);
      ("a.lt", "pub fn b() {}");
      ("a/b.lt", "pub type T = | V\npub const C: i64 = 0\npub fn f() {}");
    ]
  in
  check (files "fn f(x: a.b.T) {}");
  [%expect {| main.lt:2: E0212 |}];
  check (files "fn f(n: i64) -> i64 {\nmatch n {\na.b.C => 0\n_ => 1\n}\n}");
  [%expect {| main.lt:4: E0212 |}];
  (* [a.b.f()] calls a method [f] of the function [a.b], which has none
     (traits.method-resolution). *)
  check (files "fn f() { a.b.f() }");
  [%expect {| main.lt:2: E0314 |}]

(* program.no-cycles *)
let%expect_test "modules depend on one another without cycles" =
  main "use main";
  [%expect {| main.lt:1: E0206 |}];
  check [ ("main.lt", "use a"); ("a.lt", "use main") ];
  [%expect {| main.lt:1: E0206 |}];
  check
    [
      ("main.lt", "use b");
      ("a.lt", "\nuse main");
      ("b.lt", "use c");
      ("c.lt", "use a");
    ];
  [%expect {| main.lt:1: E0206 |}];
  (* A path that names an item makes a dependency too, placed at the path's
     first name. *)
  check
    [
      ("main.lt", "");
      ("p/a.lt", "use p.b\npub fn g() {}");
      ("p/b.lt", "use p.c");
      ("p/c.lt", "use p\nfn f() {\n  p\n    .a\n    .g()\n}");
    ];
  [%expect {| p/c.lt:3: E0206 |}];
  (* Two cycles that share a module are one error. *)
  check
    [ ("main.lt", "use a\nuse b"); ("a.lt", "use main"); ("b.lt", "use main") ];
  [%expect {| main.lt:2: E0206 |}];
  (* A module that names its own items through its parent depends on no
     module. *)
  check
    [
      ("main.lt", "use a.b");
      ("a.lt", "");
      ("a/b.lt", "use a\npub fn helper() {}\nfn f() { a.b.helper() }");
    ];
  [%expect {| ok |}]

(* program.one-value-namespace *)
let%expect_test "a local can't take the name of an imported module" =
  main
    "use std.fs\n\
     fn f(fs: i64) {}\n\
     fn g() {\n\
     let fs = 1\n\
     let _ = fs.read(\"x\")\n\
     let h = |fs: i64| fs + 1\n\
     }";
  [%expect
    {|
    main.lt:2: E0207
    main.lt:4: E0207
    main.lt:6: E0207
    |}];
  let e = final_expr (fn_t "use std.fs\nfn t() { let fs = 1\nfs }") in
  print_endline (show e);
  [%expect {| error |}]

(* program.visibility *)
let%expect_test "private items stay in their module" =
  check
    [
      ( "main.lt",
        "use a\n\
         fn f() {\n\
         let _ = a.shown\n\
         let _ = a.hidden\n\
         let _ = a.V\n\
         }\n\
         fn g(x: a.Hidden) {}" );
      ("a.lt", "pub fn shown() {}\nfn hidden() {}\ntype Hidden = | V");
    ];
  [%expect
    {|
    main.lt:4: E0213
    main.lt:5: E0213
    main.lt:7: E0213
    |}];
  main
    "type Hidden = {}\n\
     trait Secret {}\n\
     pub fn f(x: Hidden) {}\n\
     pub type P = { h: Hidden }\n\
     pub fn g<T: Secret>() {}\n\
     pub const C: Hidden = Hidden {}";
  [%expect
    {|
    main.lt:3: E0214
    main.lt:4: E0214
    main.lt:5: E0214
    main.lt:6: E0214
    |}];
  (* A member of a private type is visible nowhere outside, even when it is
     marked [pub]. *)
  main
    "type Hidden = {}\n\
     impl Hidden { pub fn new() -> Hidden { Hidden {} } }\n\
     pub type Shown = {}\n\
     impl Shown { pub fn hide(self) -> Hidden { Hidden {} } }";
  [%expect {| main.lt:4: E0214 |}]

(* errors.error-type *)
let%expect_test "syntax errors leave the rest checked" =
  check [ ("main.lt", "fn f() { g() }"); ("a.lt", "fn (") ];
  [%expect {|
    a.lt:1: E0100
    main.lt:1: E0211
    |}]
