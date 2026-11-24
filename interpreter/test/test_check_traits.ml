(* Tests of type checking against the rules on traits and methods (traits.methods and traits.method-resolution):
   where a method comes from, who may call it and the bounds it needs, and the
   traits that operators and map keys need. Each test prints a program's
   errors as conformance.diagnostic-lines compares them, leaving out warnings. *)

open Diagnostics.Errors

(* traits.methods and traits.method-resolution *)
let%expect_test "a method exists for its receiver" =
  main "fn f(x: i64) {\nx.frobnicate()\n}";
  [%expect {| main.lt:2: E0314 |}];
  (* An associated function is called through its type. *)
  main
    "type T = {}\n\
     impl T { fn make() -> T { T {} } }\n\
     fn f(t: T) -> T {\n\
     t.make()\n\
     }\n\
     fn g() -> T {\n\
     T.make()\n\
     }\n\
     fn h() -> T {\n\
     T.unmake()\n\
     }";
  [%expect {|
    main.lt:4: E0314
    main.lt:10: E0314
    |}]

(* traits.method-resolution *)
let%expect_test "methods come from the type, then traits, then bounds" =
  main
    "trait Named { fn name(self) -> str }\n\
     type T = {}\n\
     impl Named for T { fn name(self) -> str { \"t\" } }\n\
     fn f(t: T) -> str { t.name() }\n\
     fn g<A: Named>(a: A) -> str { a.name() }\n\
     fn h<A>(a: A) -> str { a.name() }";
  [%expect {| main.lt:6: E0314 |}];
  (* After methods, a record field of function type is called. *)
  main "type C = { run: fn(i64) -> i64 }\nfn f(c: C) -> i64 {\nc.run(1)\n}";
  [%expect {| ok |}]

let%expect_test "a method of two traits is called through one of them" =
  main
    "trait A { fn name(self) -> str }\n\
     trait B { fn name(self) -> str }\n\
     type T = {}\n\
     impl A for T { fn name(self) -> str { \"a\" } }\n\
     impl B for T { fn name(self) -> str { \"b\" } }\n\
     fn f(t: T) -> str {\n\
     t.name()\n\
     }\n\
     fn g(t: T) -> str {\n\
     A.name(t)\n\
     }";
  [%expect {| main.lt:7: E0319 |}]

(* traits.bounded-blocks *)
let%expect_test "a bounded block's methods need the bound" =
  main
    "type Box<T> = { item: T }\n\
     impl<T: Ord> Box<T> {\n\
     fn larger(self, other: T) -> T { if self.item < other { other } else { \
     self.item } }\n\
     }\n\
     fn f(b: Box<i64>) -> i64 { b.larger(1) }\n\
     fn g(b: Box<fn()>) {\n\
     let _ = b.larger(|| ())\n\
     }";
  [%expect {| main.lt:7: E0318 |}]

(* traits.bounds and traits.required-traits *)
let%expect_test "operators and map keys need their traits" =
  main
    "fn f<T>(a: T, b: T) -> bool {\n\
     a == b\n\
     }\n\
     fn g<T: Eq>(a: T, b: T) -> bool { a == b }";
  [%expect {| main.lt:2: E0318 |}];
  (* Floats don't implement [Hash] (traits.floats). *)
  main "fn f() {\nlet m: Map<f64, i64> = Map.new()\n}";
  [%expect {| main.lt:2: E0318 |}]

(* program.visibility *)
let%expect_test "a private method is used only in its module" =
  check
    [
      ("main.lt", "use shapes\nfn f(s: shapes.Shape) -> i64 {\ns.secret()\n}");
      ( "shapes.lt",
        "pub type Shape = | Dot\nimpl Shape { fn secret(self) -> i64 { 0 } }" );
    ];
  [%expect {| main.lt:3: E0213 |}]

(* traits.method-resolution *)
let%expect_test "a trait impl whose bound fails gives the bound's error" =
  main
    "trait Named { fn name(self) -> str }\n\
     type Box<T> = { item: T }\n\
     impl<T: Show> Named for Box<T> { fn name(self) -> str { \"{self.item}\" } }\n\
     fn f(b: Box<fn()>) -> str {\n\
     b.name()\n\
     }";
  [%expect {| main.lt:5: E0318 |}]

(* traits.impl-blocks and traits.orphan-rule *)
let%expect_test "an impl outside its homes changes no other module" =
  main "impl<T> List<T> {\nfn len(self) -> str { \"\" }\n}";
  [%expect {| main.lt:1: E0301 |}];
  main
    "impl<T> Show for List<T> {\n\
     fn show(self) -> str { \"\" }\n\
     }\n\
     fn f(xs: List<i64>) -> str { \"{xs}\" }";
  [%expect {| main.lt:1: E0303 |}]

(* traits.method-resolution and traits.structural-impls *)
let%expect_test "a type has a structural impl only if its parts can have it" =
  main
    "type Button = { show: fn() -> str }\nfn f(b: Button) -> str {\nb.show()\n}";
  [%expect {| ok |}];
  main "fn g() -> str {\n(|| \"ok\", 1).show()\n}";
  [%expect {| main.lt:2: E0318 |}]
