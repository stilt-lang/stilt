(* Tests of the order in which [test] runs a program's tests and doc
   examples (program.test-order), which conformance tests can't observe, since
   what tests print isn't part of their result (program.running-tests). Each test
   prints what the program's tests print, then their verdicts. *)

open Stilt

let test files =
  let sources =
    List.map
      (fun (file, text) ->
        {
          Program.module_path = Program.module_path file;
          file;
          text;
          package = 0;
        })
      files
  in
  match Driver.analyse sources with
  | [], Some (env, hir, program) -> (
      match Eval.test ~out:stdout env hir program with
      | Ok verdicts ->
          List.iter
            (fun (v : Eval.verdict) ->
              Printf.printf "%s:%d %b\n" v.file v.line v.passed)
            verdicts
      | Error reason -> print_endline reason)
  | _ -> print_endline "the program has errors"

let%expect_test "source order within a file, then files by path" =
  test
    [
      ( "main.lt",
        "use b\n\
         use a\n\
         /// ex: say(\"main example\")\n\
         fn say(s: str) -> bool / io { print(s)\n\
         true }\n\
         test \"second in main\" { print(\"main test\") }\n" );
      ( "b.lt",
        "test \"first in b\" { print(\"b first\") }\n\
         test \"second in b\" { print(\"b second\") }\n" );
      ("a.lt", "test \"only in a\" { print(\"a only\") }\n");
    ];
  [%expect
    {|
    a only
    b first
    b second
    main example
    main test
    a.lt:1 true
    b.lt:1 true
    b.lt:2 true
    main.lt:3 true
    main.lt:6 true
    |}]
