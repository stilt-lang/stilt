(* Tests of what names refer to (declarations.name-lookup), in each namespace and in
   patterns, and of where self, Self, break and continue may appear. Some tests
   print what a name refers to, the others a program's diagnostics as conformance.diagnostic-lines
   compares them: a file, a line and a code. *)

open Stilt
open Diagnostics
open Resolved

let%expect_test "the orders program resolves" =
  main
    {|use std.cli
use std.fs

type Order = { customer: str, qty: i64, price: f64 }

fn parse_line(n: i64, text: str) -> Order / raise<str> {
  let [customer, q, p] = text.split(",") else raise "line {n}: expected 3 fields"
  let qty = q.to_i64() else raise "line {n}: bad qty {q}"
  let price = p.to_f64() else raise "line {n}: bad price {p}"
  Order { customer, qty, price }
}

fn main() / {io, raise<str>} {
  let path = cli.arg(0) else raise "usage: orders <file>"
  let lines = try fs.read_lines(path) catch _ => raise "cannot read {path}"
  let orders = try lines.skip(1).enumerate(2).map(|(n, l)| parse_line(n, l))
  for o in orders {
    print("{o.customer}")
  }
}|};
  [%expect {| ok |}]

let%expect_test "what names refer to" =
  refers "fn x() {}\nfn t() { let x = 1\nx }";
  [%expect {| local x |}];
  refers "fn t() { print }";
  [%expect {| fn std.prelude.print |}];
  refers "use std.fs\nfn t() { fs.read }";
  [%expect {| fn std.fs.read |}];
  refers "use std\nfn t() { std.fs.read }";
  [%expect {| fn std.fs.read |}];
  refers "use std.io\nfn t() { io.NotFound(\"x\") }";
  [%expect {| call of (variant std.io.NotFound) |}];
  refers "fn t(p: (i64, i64)) { p.0 }";
  [%expect {| field 0 of (local p) |}];
  refers "fn t() { i64.MAX }";
  [%expect {| member MAX of type std.prelude.i64 |}];
  refers "fn t<T: Ord>() { T.compare }";
  [%expect {| member compare of type parameter T |}];
  refers "fn t() { Show.show }";
  [%expect {| member show of trait std.prelude.Show |}];
  refers "type T = {}\nimpl T {\nfn f() {}\nfn t() { Self.f }\n}";
  [%expect {| member f of type main.T |}];
  refers "fn t() { missing.x }";
  [%expect {| error |}]

(* declarations.unique-names *)
let%expect_test "a type comes first before a member" =
  refers
    "type UserId = | UserId(i64)\n\
     impl UserId { fn new() -> UserId { UserId(0) } }\n\
     fn t() { UserId.new }";
  [%expect {| member new of type main.UserId |}];
  refers "type UserId = | UserId(i64)\nfn t() { UserId }";
  [%expect {| variant main.UserId |}]

(* The variables an expression's locals refer to, by declaration. *)
let%expect_test "the alternatives of an or-pattern bind the same variables" =
  let f =
    fn_t
      "type T = | A(i64) | B(i64)\n\
       fn t(v: T) -> i64 { match v { A(x) | B(x) => x } }"
  in
  let rec binds (p : Hir.pattern) =
    match p.desc with
    | P_bind v -> [ v.id ]
    | P_variant (_, ps) | P_bare (_, ps, _) | P_or ps ->
        List.concat_map binds ps
    | _ -> []
  in
  (match (final_expr f).desc with
  | Match (_, [ { pattern; body = { desc = Local v; _ }; _ } ]) ->
      let ids = binds pattern in
      Printf.printf "%b\n" (List.for_all (( = ) v.id) ids && List.length ids = 2)
  | _ -> print_endline "unexpected tree");
  [%expect {| true |}]

let%expect_test "names resolve in their namespace" =
  main "fn f() { g() }\nfn h(x: Missing) {}\nfn k() / e {}";
  [%expect
    {|
    main.lt:1: E0211
    main.lt:2: E0211
    main.lt:3: E0211
    |}];
  main "use std.fs\nfn f() { fs.reed() }\nfn g() { std.fs.read() }";
  [%expect {|
    main.lt:2: E0211
    main.lt:3: E0211
    |}];
  main
    "use std.fs\n\
     type R = {}\n\
     fn f() { let _ = fs }\n\
     fn g() { let _ = R }\n\
     fn h(x: Show) {}\n\
     fn k<T: R>() {}";
  [%expect
    {|
    main.lt:3: E0212
    main.lt:4: E0212
    main.lt:5: E0212
    main.lt:6: E0212
    |}];
  (* A name of the wrong kind is E0212 whatever the form of its path. *)
  main
    "use std.fs\n\
     type Shape = | Dot\n\
     const ONE: i64 = 1\n\
     fn f(a: Dot,\n\
     b: ONE,\n\
     c: fs,\n\
     d: print,\n\
     e: fs.IoError) {}";
  [%expect
    {|
    main.lt:4: E0212
    main.lt:5: E0212
    main.lt:6: E0212
    main.lt:7: E0212
    main.lt:8: E0211
    |}]

let%expect_test "patterns name variants, constants and record types" =
  main
    "use std.io\n\
     const ZERO: i64 = 0\n\
     type P = { x: i64 }\n\
     fn f(e: io.IoError, n: i64, p: P) {\n\
     let _ = match e { io.NotFound(_) => 0, _ => 1 }\n\
     let _ = match n { ZERO => 0, i64.MAX => 1, _ => 2 }\n\
     let P { x } = p\n\
     }";
  [%expect {| ok |}];
  main
    "const C: i64 = 0\n\
     type P = {}\n\
     fn f(n: i64) {\n\
     let _ = match n { C(x) => x, _ => 0 }\n\
     let _ = match n { P => 0, _ => 1 }\n\
     let _ = match n { Q => 0, _ => 1 }\n\
     }";
  [%expect
    {|
    main.lt:4: E0212
    main.lt:5: E0212
    main.lt:6: E0211
    |}]

(* traits.bounded-blocks *)
let%expect_test "self belongs to methods, and Self to impl and trait blocks" =
  main "type T = {}\nimpl T { fn get(self) -> T { self } }";
  [%expect {| ok |}];
  main "fn f(self) {}\ntype T = {}\nimpl T { fn g() -> T { self } }";
  [%expect {|
    main.lt:1: E0215
    main.lt:3: E0215
    |}];
  main "fn f() -> Self {\nSelf {}\n}";
  [%expect {|
    main.lt:1: E0215
    main.lt:2: E0215
    |}]

(* expressions.break-and-continue *)
let%expect_test "break and continue belong to the body of a loop" =
  main
    "fn f(xs: List<i64>) {\n\
     for x in xs {\n\
     while x > 0 {\n\
     if x > 1 { break }\n\
     }\n\
     continue\n\
     }\n\
     }";
  [%expect {| ok |}];
  main "fn f() {\nbreak\n}\nfn g() { loop {\nlet h = || continue\n} }";
  [%expect {|
    main.lt:2: E0216
    main.lt:5: E0216
    |}]

(* patterns.floats *)
let%expect_test "alternatives bind the same names" =
  main
    "type T = | A(i64) | B(i64) | C\n\
     fn f(t: T) -> i64 { match t { A(x) | B(x) => x, C => 0 } }";
  [%expect {| ok |}];
  main
    "type T = | A(i64) | B(i64) | C\n\
     fn f(t: T) -> i64 {\n\
     match t {\n\
     A(x) | B(y) => y\n\
     C | A(z) => 0\n\
     B(_) => 0\n\
     }\n\
     }";
  [%expect {|
    main.lt:4: E0217
    main.lt:5: E0217
    |}];
  (* Each error is reported once, and causes no other. *)
  main
    "type T = | A(i64) | B(i64)\n\
     fn f(t: (T, i64), u: (i64, T)) {\n\
     match t { (A(x) | B(y), y) => {} }\n\
     match u { (x, A(x) | B(x)) => {} }\n\
     }";
  [%expect {|
    main.lt:3: E0217
    main.lt:4: E0208
    |}];
  (* A name that some alternative doesn't bind has the error type. *)
  let e =
    final_expr
      (fn_t
         "type T = | A(i64) | B(i64)\n\
          fn t(v: T) -> i64 { match v { A(x) | B(y) => y } }")
  in
  (match e.desc with
  | Match (_, [ { body; _ } ]) -> print_endline (show body)
  | _ -> print_endline "unexpected tree");
  [%expect {| error |}]
