(* Tests of the warnings for holes (declarations.typed-holes) and for commented-out
   code (lexical.commented-out-code). Each test prints a program's diagnostics as conformance.diagnostic-lines
   compares them, warnings included. *)

open Diagnostics

(* declarations.typed-holes *)
let%expect_test "each hole gets a warning" =
  main "fn f() -> i64 {\nlet a: i64 = ?\na + ?\n}";
  [%expect {|
    main.lt:2: W0300
    main.lt:3: W0300 |}]

(* lexical.commented-out-code *)
let%expect_test "commented-out code gets a warning" =
  main
    "// print(\"old\")\n\
     // fallthrough\n\
     // 42\n\
     // -1\n\
     // TODO: tidy this up\n\
     // let x = 1\n\
     // fn old() {}\n\
     /// A doc comment, with `f(x)`.\n\
     fn f(x: i64) -> i64 {\n\
     x // x + 1\n\
     }";
  [%expect
    {|
    main.lt:1: W0001
    main.lt:6: W0001
    main.lt:7: W0001
    main.lt:10: W0001 |}];
  (* A program with an error still gets them, since they are outside any
     body. *)
  main "// f()\nfn f() -> i64 {\n\"no\"\n}";
  [%expect {|
    main.lt:1: W0001
    main.lt:3: E0311 |}]

(* lexical.commented-out-code *)
let%expect_test "a comment of one token is exempt" =
  main
    "// \"hello {name}\"\n\
     // ()\n\
     // (unused)\n\
     // - retries\n\
     // ?\n\
     // true\n\
     // -1.5\n\
     // i.e. done\n\
     // \"a {x}\" == \"b\"\n\
     fn f() {}";
  [%expect {|
    main.lt:8: W0001
    main.lt:9: W0001 |}]
