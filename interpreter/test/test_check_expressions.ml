(* Tests of type checking against the rules on the types of expressions
   (types.expected-types and expressions.arguments): the type each context expects, calls and their arguments, places,
   fields, and the types a body leaves undecided. Each test prints a program's
   errors as conformance.diagnostic-lines compares them, leaving out warnings. *)

open Diagnostics.Errors

(* types.expected-types *)
let%expect_test "an expression has the type its context expects" =
  main "fn f() -> i64 {\nlet s: str = 1\n\"a\"\n}";
  [%expect {|
    main.lt:2: E0311
    main.lt:3: E0311
    |}];
  main "fn g(x: bool) {}\nfn f() {\ng(1)\n}";
  [%expect {| main.lt:3: E0311 |}];
  (* [Never] fits anywhere (declarations.never). *)
  main "fn f(o: Option<i64>) -> i64 {\nlet x: i64 = o else return 0\nx\n}";
  [%expect {| ok |}]

(* expressions.option-fallback *)
let%expect_test "the else fallback applies to an option" =
  main
    "fn f(o: Option<i64>, r: Result<i64, str>) -> i64 {\n\
     let a = o else 0\n\
     let b = r else 0\n\
     a + b\n\
     }";
  [%expect {| main.lt:3: E0311 |}]

(* expressions.if and expressions.loop-types *)
let%expect_test "if, loop, while and for have their types" =
  main "fn f() -> i64 {\nloop {}\n}";
  [%expect {| ok |}];
  main "fn f() -> i64 {\nloop { break }\n}";
  [%expect {| main.lt:2: E0311 |}];
  main "fn f(c: bool) -> i64 {\nif c { let x = 1 } else { 2 }\n}";
  [%expect {| main.lt:2: E0311 |}];
  main
    "fn f(n: i64, m: Map<str, i64>) -> i64 {\n\
     var t = 0\n\
     for i in 0..n { t += i }\n\
     for (k, v) in m { t += v }\n\
     while t > 100 { t -= 1 }\n\
     t\n\
     }";
  [%expect {| ok |}];
  main "fn f(n: i64) {\nfor x in n {}\n}";
  [%expect {| main.lt:2: E0311 |}]

(* types.expected-types *)
let%expect_test "only a function is called" =
  main "fn f(x: i64) -> i64 {\nx(1)\n}";
  [%expect {| main.lt:2: E0311 |}]

(* types.known-types, and traits.method-resolution *)
let%expect_test "a receiver's type is known where it is used" =
  main "fn f() {\nlet g = |x| x.len()\n}";
  [%expect {| main.lt:2: E0312 |}];
  main "fn f() {\nlet g = |x: str| x.len()\n}";
  [%expect {| ok |}];
  (* A literal gets its default type there (numbers.literal-defaults). *)
  main "fn f() -> i64 {\nlet x = 5\nx.abs()\n}";
  [%expect {| ok |}];
  main "fn f() -> f64 {\nvar total = 0\ntotal += 1.5\ntotal\n}";
  [%expect {| ok |}]

(* types.undecided-types, and declarations.typed-holes *)
let%expect_test "a type that the body leaves undecided is an error" =
  main "fn f() {\nlet xs = []\n}";
  [%expect {| main.lt:2: E0312 |}];
  main "fn f() {\nlet x = ?\n}";
  [%expect {| main.lt:2: E0312 |}];
  main "fn f() -> i64 {\nlet x = ?\nx\n}";
  [%expect {| ok |}];
  (* Only when the body has no other error (errors.root-causes). *)
  main "fn f() {\nlet xs = []\nlet y: i64 = \"a\"\n}";
  [%expect {| main.lt:3: E0311 |}]

(* types.field-access *)
let%expect_test "a field exists in its record or tuple" =
  main "type P = { x: i64 }\nfn f(p: P) -> i64 {\np.y\n}";
  [%expect {| main.lt:3: E0313 |}];
  main "fn f(t: (i64, i64)) -> i64 {\nt.2\n}";
  [%expect {| main.lt:2: E0313 |}];
  main "fn f(t: (i64, str)) -> str {\nt.1\n}";
  [%expect {| ok |}]

(* expressions.struct-literal-fields *)
let%expect_test "a record literal gives each field once" =
  main
    "type P = { x: i64, y: i64 }\n\
     fn f() -> P {\n\
     let a = P { x: 1, y: 2, z: 3 }\n\
     let b = P { x: 1, x: 2, y: 3 }\n\
     P { x: 1 }\n\
     }";
  [%expect
    {|
    main.lt:3: E0313
    main.lt:4: E0316
    main.lt:5: E0316
    |}];
  main "type P = { x: i64, y: i64 }\nfn f(x: i64) -> P {\nP { x, y: 2 }\n}";
  [%expect {| ok |}]

(* expressions.arguments *)
let%expect_test "a call passes one argument per parameter" =
  main "fn g(x: i64) {}\nfn f() {\ng(1, 2)\n}";
  [%expect {| main.lt:3: E0315 |}];
  main "fn f() -> Option<i64> {\nSome(1, 2)\n}";
  [%expect {| main.lt:2: E0315 |}];
  (* A closure takes the parameters its expected type has (expressions.closure-parameter-types). *)
  main
    "fn apply(h: fn(i64) -> i64) -> i64 { h(1) }\n\
     fn f() -> i64 {\n\
     apply(|a, b| a)\n\
     }";
  [%expect {| main.lt:3: E0315 |}]

(* std.lists and std.maps *)
let%expect_test "lists and maps can be indexed" =
  main "fn f(x: i64) -> i64 {\nx[0]\n}";
  [%expect {| main.lt:2: E0317 |}];
  main "fn f(xs: List<str>, m: Map<str, i64>) -> i64 {\nm[xs[0]]\n}";
  [%expect {| ok |}]

(* expressions.inout-arguments *)
let%expect_test "an inout argument is marked at the call" =
  main
    "fn bump(inout n: i64) { n += 1 }\n\
     fn show(n: i64) {}\n\
     fn f() {\n\
     var a = 1\n\
     bump(a)\n\
     bump(inout a)\n\
     show(inout a)\n\
     }";
  [%expect {|
    main.lt:5: E0400
    main.lt:7: E0400
    |}]

(* expressions.inout-arguments and expressions.places *)
let%expect_test "only a place is assigned or passed inout" =
  main
    "fn bump(inout n: i64) { n += 1 }\n\
     fn f() {\n\
     bump(inout 1)\n\
     [1, 2].push(3)\n\
     }";
  [%expect {|
    main.lt:3: E0401
    main.lt:4: E0401
    |}]

(* expressions.unused-values *)
let%expect_test "a value isn't left unused" =
  main "fn f(xs: List<i64>) {\nxs.len()\nlet _ = xs.len()\n}";
  [%expect {| main.lt:2: E0322 |}];
  main "fn f(xs: List<i64>) -> i64 {\nreturn 0\nxs.len()\n}";
  [%expect {| ok |}]

(* expressions.if *)
let%expect_test "an if without else has no value" =
  main "fn f(c: bool) {\nif c { 1 }\nif c { return }\n}";
  [%expect {| main.lt:2: E0323 |}];
  (* The missing [else] is the one error. *)
  main "fn f(c: bool) -> i64 {\nif c { 1 }\n}";
  [%expect {| main.lt:2: E0323 |}];
  main "fn f(c: bool) -> i64 {\nif c { return 1 }\n}";
  [%expect {| main.lt:2: E0311 |}]

(* expressions.key-paths *)
let%expect_test "a key path stands where a function is expected" =
  main
    "type P = { x: i64, tags: List<str> }\n\
     fn a(ps: List<P>) -> List<i64> { ps.map(.x) }\n\
     fn b(ps: List<P>) -> List<str> { ps.map(.tags[0]) }\n\
     fn c(ps: List<(i64, str)>) -> List<str> { ps.map(.1) }\n\
     fn d(ps: List<P>) -> List<i64> { ps.map(.tags.len()) }\n\
     fn e(ps: List<List<P>>) -> List<List<i64>> { ps.map(.map(.x)) }";
  [%expect {| ok |}];
  main "fn f() {\nlet k = .x\n}";
  [%expect {| main.lt:2: E0324 |}]

(* std.precision, std.integer-kinds, std.scientific-notation and std.invalid-specs *)
let%expect_test "a format spec applies to its value's type" =
  main
    "fn f(s: str, x: f64, n: i64) -> str {\n\
     \"{s:>8}{x:.2}{x:e}{n:x}{n:8b}{s:*^5}\"\n\
     }";
  [%expect {| ok |}];
  main "fn f(s: str) -> str {\n\"{s:x}\"\n}";
  [%expect {| main.lt:2: E0325 |}];
  main "fn f(n: i64) -> str {\n\"{n:.2}\"\n}";
  [%expect {| main.lt:2: E0325 |}];
  main "fn f(n: i64) -> str {\n\"{n:e}\"\n}";
  [%expect {| main.lt:2: E0325 |}]

(* types.expected-types *)
let%expect_test "no type contains itself" =
  main "fn f() {\nvar g = || ()\ng = || raise g\n}";
  [%expect {| main.lt:3: E0311 |}]

(* expressions.break-and-continue *)
let%expect_test "a break in a nested loop's head exits the outer loop" =
  main "fn f() -> i64 {\nloop { while (break) {} }\n}";
  [%expect {| main.lt:2: E0311 |}];
  main
    "fn f(c: bool) -> i64 {\n\
     loop { for i in 0..(if c { break } else { 3 }) {} }\n\
     }";
  [%expect {| main.lt:2: E0311 |}]

(* declarations.never *)
let%expect_test "Never converts inside tuples and operators" =
  main
    "fn a() -> (i64, i64) {\n\
     (panic(\"a\"), 1)\n\
     }\n\
     fn b() -> bool {\n\
     panic(\"a\") && true\n\
     }\n\
     fn c() -> i64 {\n\
     panic(\"a\") + 1\n\
     }\n\
     fn d() -> i64 {\n\
     panic(\"a\") else 1\n\
     }\n\
     fn e() -> bool {\n\
     panic(\"a\") == 1\n\
     }";
  [%expect {| ok |}]

(* declarations.constructors *)
let%expect_test "a variant without a payload isn't called" =
  main "fn f() -> Option<i64> {\nNone()\n}";
  [%expect {| main.lt:2: E0311 |}]

(* traits.method-resolution, and effects.function-values *)
let%expect_test "a tuple's element that holds a function is called" =
  main
    "fn quiet() {}\n\
     fn f(t: (fn(i64) -> i64, str)) -> i64 {\n\
     let a = t.0(1)\n\
     let u: (fn() / io, i64) = (quiet, 1)\n\
     (t.0)(a)\n\
     }";
  [%expect {| ok |}]
