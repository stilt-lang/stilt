(* Tests of user-defined effects and handlers (handlers.declaring-effect and handlers.handler-literals) and of [async]
   (tasks.async): the errors that checking reports, as conformance.diagnostic-lines compares them, and
   what programs write when they run, followed by their exit status. *)

open Stilt

let run text =
  match Driver.analyse (Diagnostics.sources [ ("main.lt", text) ]) with
  | [], Some (env, hir, program) -> (
      match Eval.run env hir program ~args:[] with
      | Some status -> Printf.printf "exit %d\n" status
      | None -> print_endline "no main")
  | _ -> print_endline "the program has errors"

let ask = "effect Ask {\nfn ask() -> i64\n}\n"
let log = "effect Log {\nfn log(s: str)\n}\n"

(* handlers.effects-in-rows *)
let%expect_test "a row holds one instance of an effect" =
  Diagnostics.Errors.main
    "effect State<S> {\nfn get() -> S\n}\nfn f() / {State<i64>, State<str>} {}";
  [%expect {| main.lt:4: E0515 |}]

(* handlers.performing-operation *)
let%expect_test "a performance fits the row around it" =
  Diagnostics.Errors.main (ask ^ "fn f() -> i64 {\nAsk.ask()\n}");
  [%expect {| main.lt:5: E0502 |}];
  Diagnostics.Errors.main (ask ^ "fn f() -> i64 / Ask {\nAsk.ask()\n}");
  [%expect {| ok |}]

(* handlers.handler-types *)
let%expect_test "a handler implements each operation once" =
  Diagnostics.Errors.main
    (ask
   ^ "effect Two {\n\
      fn a()\n\
      fn b()\n\
      }\n\
      fn f() / io {\n\
      let h = handler Two { fn a() {} }\n\
      }");
  [%expect {| main.lt:9: E0511 |}]

(* handlers.resuming *)
let%expect_test "resume only where a handler takes control" =
  Diagnostics.Errors.main
    (ask ^ "fn f() {\nlet h = handler Ask { fn ask() -> i64 { resume(1) } }\n}");
  [%expect {| main.lt:5: E0513 |}]

(* handlers.resuming *)
let%expect_test "resume at most once on each path" =
  Diagnostics.Errors.main
    (ask
   ^ "fn f() {\n\
      let h = handler Ask -> i64 {\n\
      fn ask() -> i64 {\n\
      let a = resume(1)\n\
      resume(2)\n\
      }\n\
      }\n\
      }");
  [%expect {| main.lt:8: E0514 |}];
  (* Two branches that each resume are two paths. *)
  Diagnostics.Errors.main
    (ask
   ^ "fn f(b: bool) {\n\
      let h = handler Ask -> i64 {\n\
      fn ask() -> i64 {\n\
      if b { resume(1) } else { resume(2) }\n\
      }\n\
      }\n\
      }");
  [%expect {| ok |}];
  Diagnostics.Errors.main
    (ask
   ^ "fn f() {\n\
      let h = handler Ask -> i64 {\n\
      fn ask() -> i64 {\n\
      var n = 0\n\
      while n < 2 { n = resume(n) }\n\
      n\n\
      }\n\
      }\n\
      }");
  [%expect {| main.lt:8: E0514 |}]

(* handlers.no-effect-reaches-main *)
let%expect_test "no user-defined effect reaches main" =
  Diagnostics.Errors.main (ask ^ "fn main() / Ask {}");
  [%expect {| main.lt:4: E0512 |}];
  Diagnostics.Errors.main (ask ^ "fn main() {\nlet n = Ask.ask()\n}");
  [%expect {| main.lt:5: E0512 |}]

(* handlers.with: a handler inside another of its effect hides it, and its
   own bodies perform its effect on the handler outside it. *)
let%expect_test "the nearest handler runs" =
  run
    (log
   ^ "fn work() / Log {\n\
      Log.log(\"a\")\n\
      Log.log(\"b\")\n\
      }\n\
      fn main() / io {\n\
      let outer = handler Log { fn log(s: str) { print(\"outer {s}\") } }\n\
      let inner = handler Log { fn log(s: str) { Log.log(\"inner {s}\") } }\n\
      with outer {\n\
      work()\n\
      with inner { work() }\n\
      }\n\
      }");
  [%expect
    {|
    outer a
    outer b
    outer inner a
    outer inner b
    exit 0
    |}]

(* handlers.resuming: a body that never resumes ends the [with] with its value,
   and the rest of the block never runs. *)
let%expect_test "a handler that takes control" =
  run
    (ask
   ^ "fn main() / io {\n\
      let stop = handler Ask -> i64 { fn ask() -> i64 { 7 } }\n\
      let n = with stop {\n\
      print(\"before\")\n\
      let x = Ask.ask()\n\
      print(\"never\")\n\
      x + 1\n\
      }\n\
      print(\"{n}\")\n\
      let twice = handler Ask -> i64 {\n\
      fn ask() -> i64 { resume(20) * 2 }\n\
      }\n\
      print(\"{with twice { Ask.ask() + 1 }}\")\n\
      }");
  [%expect {|
    before
    7
    42
    exit 0
    |}]

(* tasks.sequential-run: [spawn] runs the task's function to its end before it
   returns, and [await] gives the value the task ended with. *)
let%expect_test "tasks run sequentially under main" =
  run
    "use std.task\n\
     fn main() / {io, async} {\n\
     let t = task.spawn(|| {\n\
     print(\"in task\")\n\
     2\n\
     })\n\
     print(\"spawned\")\n\
     let v = t.await()\n\
     print(\"{v}\")\n\
     }";
  [%expect {|
    in task
    spawned
    2
    exit 0
    |}]
