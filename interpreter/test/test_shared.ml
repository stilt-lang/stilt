(* Tests of shared state, [when] and scopes (shared.when and tasks.scopes) and of deterministic
   parallelism (par.std-par): the errors that checking reports, as conformance.diagnostic-lines compares
   them, and what programs write when they run, followed by their exit
   status. *)

open Stilt

let run text =
  match Driver.analyse (Diagnostics.sources [ ("main.lt", text) ]) with
  | [], Some (env, hir, program) -> (
      match Eval.run env hir program ~args:[] with
      | Some status -> Printf.printf "exit %d\n" status
      | None -> print_endline "no main")
  | _ -> print_endline "the program has errors"

let header = "use std.sync\nuse std.task\nuse std.par\nuse std.view\n"

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error d -> print_endline (Diagnostic.to_string d)

(* shared.when and shared.locks, and reference/03-syntax.md: [locks] is a keyword only
   where a limit can stand. *)
let%expect_test "when and locks parse" =
  show "fn t(a: S, b: S) without locks {\nwhen a, b { a = b }\n}";
  [%expect
    {| (module (fn t () ((a S) (b S)) (tuple) (row) (without locks) (block (when (a b) (block (= a b)))))) |}];
  show "fn locks() {}";
  [%expect {| (module (fn locks () () (tuple) (row) (block))) |}]

(* shared.when *)
let%expect_test "when holds locals and parameters only" =
  Diagnostics.Errors.main (header ^ "fn f() {}\nfn g() {\nwhen f { }\n}");
  [%expect {| main.lt:7: E0433 |}]

(* shared.std-sync *)
let%expect_test "a shared value is indexed only inside when" =
  Diagnostics.Errors.main
    (header ^ "fn f(s: sync.Shared<List<i64>>) -> i64 {\ns[0]\n}");
  [%expect {| main.lt:6: E0317 |}]

(* shared.locks: a call through a closure literal written in the block is
   a site of the block. *)
let%expect_test "a when inside a closure inside a when" =
  Diagnostics.Errors.main
    (header
   ^ "fn f(a: sync.Shared<i64>, b: sync.Shared<i64>) {\n\
      when a {\n\
      let g = || when b { b }\n\
      a = g()\n\
      }\n\
      }");
  [%expect {| main.lt:7: E0430 |}]

(* shared.locks: [locks] passes through calls. *)
let%expect_test "without locks reaches through calls" =
  Diagnostics.Errors.main
    (header
   ^ "fn touch(a: sync.Shared<i64>) {\n\
      when a { a += 1 }\n\
      }\n\
      fn f(a: sync.Shared<i64>) without locks {\n\
      touch(a)\n\
      }");
  [%expect {| main.lt:9: E0204 |}]

(* shared.tasks-and-modes *)
let%expect_test "a scope's task captures no view" =
  Diagnostics.Errors.main
    (header
   ^ "fn f(xs: List<i64>) -> i64 / {io, async, raise<i64>} {\n\
      let v = view.View.all(xs)\n\
      try task.scope(|s| {\n\
      let t = try s.spawn(|| v.len())\n\
      t.await()\n\
      })\n\
      }");
  [%expect {| main.lt:8: E0432 |}]

(* tasks.scope-that-escapes *)
let%expect_test "a scope that leaves its function" =
  Diagnostics.Errors.main
    (header
   ^ "fn f() -> task.Scope<i64> / {io, async, raise<i64>} {\n\
      try task.scope(|s| s)\n\
      }");
  [%expect {| main.lt:6: E0434 |}]

(* par.what-runs-in-parallel: a closure that a binding holds is checked as its literal
   is. *)
let%expect_test "a bound closure that reaches a shared value" =
  Diagnostics.Errors.main
    (header
   ^ "fn f(s: sync.Shared<i64>) -> List<i64> {\n\
      let g = |x: i64| when s { s + x }\n\
      par.map([1], g)\n\
      }");
  [%expect {| main.lt:7: E0431 |}]

(* shared.when: two names that reach one value are one place, and a
   write stays when a raise leaves the block. *)
let%expect_test "one place, and writes that stay" =
  run
    (header
   ^ "fn main() / io {\n\
      let c = sync.Shared.new(1)\n\
      let d = c\n\
      when c, d {\n\
      c += 1\n\
      d *= 10\n\
      }\n\
      let r = try {\n\
      when c {\n\
      c += 5\n\
      if c > 0 { raise c }\n\
      c\n\
      }\n\
      } catch e => e\n\
      print(\"{r} {when d { d }}\")\n\
      }");
  [%expect {|
    25 25
    exit 0
    |}]

(* par.fold-tree: the first ⌊n/2⌋ elements, then the rest. *)
let%expect_test "the tree of a fold" =
  run
    (header
   ^ "fn j(p: str, q: str) -> str { \"({p}{q})\" }\n\
      fn main() / io {\n\
      print(par.fold([\"a\", \"b\"], \"e\", j))\n\
      print(par.fold([\"a\", \"b\", \"c\", \"d\", \"e\"], \"e\", j))\n\
      print(par.fold([\"a\", \"b\", \"c\", \"d\", \"e\", \"f\", \"g\"], \"e\", \
      j))\n\
      }");
  [%expect
    {|
    (ab)
    ((ab)(c(de)))
    ((a(bc))((de)(fg)))
    exit 0
    |}]

(* par.sequential-meaning and par.panics: [both] runs [f], then [g], so the panic of [f] is
   the one reported. *)
let%expect_test "both panics in order" =
  run
    (header
   ^ "fn boom(s: str) -> i64 { panic(s) }\n\
      fn main() / io {\n\
      print(\"start\")\n\
      let _ = par.both(|| boom(\"f\"), || boom(\"g\"))\n\
      }");
  [%expect
    {|
    start
    panic: explicit: "f"
      at main.lt:5:26
    exit 101
    |}]

(* tasks.scopes and tasks.scope-failure: a task that raises raises at [s.spawn], and the
   tasks after it never start. *)
let%expect_test "a scope stops at its first raise" =
  run
    (header
   ^ "fn bad(n: i64) -> i64 / raise<i64> { if n > 1 { raise n } else { n } }\n\
      fn main() / io {\n\
      with task.sequential() {\n\
      let r = try task.scope(|s| {\n\
      let a = try s.spawn(|| { print(\"one\"); bad(1) })\n\
      let b = try s.spawn(|| bad(2))\n\
      let c = try s.spawn(|| { print(\"three\"); bad(3) })\n\
      a.await() + b.await() + c.await()\n\
      }) catch e => e * 100\n\
      print(\"{r}\")\n\
      }\n\
      }");
  [%expect {|
    one
    200
    exit 0
    |}]
