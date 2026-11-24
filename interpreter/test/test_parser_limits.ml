(* Tests of the parser on [without] clauses (program.header-limits; declarations.limits)
   and on the contextual keywords (lexical.contextual-keywords). Each test prints the tree
   of a source text, or its first syntax error. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

let%expect_test "module headers" =
  show "module billing.invoice\n  without alloc,\n    panic\n\nuse std.fs";
  [%expect
    {| (module (header billing.invoice (without alloc panic)) (use std.fs)) |}];
  (* Name resolution reports a second clause (program.header-limits). *)
  show "module m; without alloc; without panic, alloc";
  [%expect {| (module (header m (without alloc) (without panic alloc))) |}];
  (* A clause may follow the path on its line (program.header-limits). *)
  show "module m without alloc\nwithout panic";
  [%expect {| (module (header m (without alloc) (without panic))) |}];
  show "module m\nwithout expert";
  [%expect {| t.lt:2:9: E0100: unexpected `expert` |}];
  (* A tier is no limit (program.tiers). *)
  show "module m\nwithout panic, advanced";
  [%expect {| t.lt:2:16: E0100: unexpected `advanced` |}];
  show "module m\nwithout panic,\nfn f() {}";
  [%expect {| t.lt:3:1: E0100: unexpected `fn` |}];
  show "module m\nuse std.fs\nwithout panic";
  [%expect {| t.lt:3:1: E0100: unexpected `without` |}]

let%expect_test "function clauses" =
  show
    "fn f(x: i64) -> i64 / io without panic, alloc { x }\n\
     fn g() without alloc = ?\n\
     fn h() -> str without panic {}";
  [%expect
    {| (module (fn f () ((x i64)) i64 (row io) (without panic alloc) (block x)) (fn g () () (tuple) (row) (without alloc) ?) (fn h () () str (row) (without panic) (block))) |}];
  show "fn f() without systems {}";
  [%expect {| t.lt:1:16: E0100: unexpected `systems` |}];
  show
    "trait T {\n  fn a(self) -> i64\n  fn b(self) -> i64 without panic { 1 }\n}";
  [%expect
    {| (module (trait T (fn a () (self) i64 (row)) (fn b () (self) i64 (row) (without panic) (block 1)))) |}];
  show "trait T { fn a(self) without panic }";
  [%expect {| t.lt:1:36: E0100: unexpected `}` |}];
  (* A line that begins with [without] and a limit continues the signature,
     and a [without] that ends its line starts no clause (lexical.continuation-lines). *)
  show "fn f() -> i64\n  without panic { 1 }";
  [%expect {| (module (fn f () () i64 (row) (without panic) (block 1))) |}];
  show "fn f() -> i64\n  without\n  panic { 1 }";
  [%expect {| t.lt:1:11: E0100: unexpected end of the statement |}]

let%expect_test "contextual keywords are read where the grammar accepts them" =
  show "module m\nfoo\n`";
  [%expect {| t.lt:2:1: E0100: unexpected `foo` |}];
  show "module m\nwithout expert\n`";
  [%expect {| t.lt:2:9: E0100: unexpected `expert` |}];
  show "module m\nwithout meta\n`";
  [%expect {| t.lt:2:9: E0100: unexpected `meta` |}];
  show "fn f() { try g() catch e since\n`\n}";
  [%expect {| t.lt:1:26: E0100: unexpected `since` |}];
  show "fn f(io: i64, because: i64) / io { let total = because; tier(io) }";
  [%expect
    {| (module (fn f () ((io i64) (because i64)) (tuple) (row io) (block (let total because) (call tier io)))) |}];
  show
    "fn f(without: i64, panic: i64) -> i64 without alloc { let meta = without; \
     alloc(panic) }";
  [%expect
    {| (module (fn f () ((without i64) (panic i64)) i64 (row) (without alloc) (block (let meta without) (call alloc panic)))) |}];
  show "fn g<without>() / without {}\nfn h<e>() / e without panic {}";
  [%expect
    {| (module (fn g (without) () (tuple) (row without) (block)) (fn h (e) () (tuple) (row e) (without panic) (block))) |}];
  show
    "use std.io\nfn f() / {io, e} { try g() catch because because \"r\" => 0 }";
  [%expect
    {| (module (use std.io) (fn f () () (tuple) (row io e) (block (try (call g) (catch (arm because (because "r") 0)))))) |}]

(* facts.spelling *)
let%expect_test "div and copy are limits only after without" =
  show "module m\nwithout panic, div\nfn f() without div, copy, alloc {}";
  [%expect
    {| (module (header m (without panic div)) (fn f () () (tuple) (row) (without div copy alloc) (block))) |}];
  show
    "fn copy<div>(div: i64, escaping f: fn() / div) -> i64 / div { let copy = \
     div; copy }";
  [%expect
    {| (module (fn copy (div) ((div i64) (escaping f (fn () (tuple) (row div)))) i64 (row div) (block (let copy div) copy))) |}];
  show "fn f() without total {}";
  [%expect {| t.lt:1:16: E0100: unexpected `total` |}]

(* facts.without *)
let%expect_test "capabilities are limits only after without" =
  show
    "module m\n\
     without fs, net\n\
     fn f() without clock, env, console, rand, spawn {}";
  [%expect
    {| (module (header m (without fs net)) (fn f () () (tuple) (row) (without clock env console rand spawn) (block))) |}];
  show
    "fn net<fs>(clock: i64, escaping f: fn() / fs) -> i64 / fs { let env = \
     clock; env }";
  [%expect
    {| (module (fn net (fs) ((clock i64) (escaping f (fn () (tuple) (row fs)))) i64 (row fs) (block (let env clock) env))) |}];
  show "fn f() without files {}";
  [%expect {| t.lt:1:16: E0100: unexpected `files` |}]
