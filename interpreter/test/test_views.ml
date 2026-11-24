(* Tests of views and iterators: the native type declaration (views.std-view), a module's tier (views.std-view), the errors of phase 2 (views.viewable-types, views.escaping and views.change-while-viewed),
   and the order in which an iterator asks for its elements (views.laziness), which
   only panics observe in a conformance test. *)

open Stilt
open Diagnostics

(* views.std-view: only the standard library declares native types; a
   program's [type T = ?] is the alias form, a syntax error (declarations.no-aliases). *)
let%expect_test "a native type is the standard library's" =
  let parse ~native text =
    match Syntax.parse ~native ~file:"t.lt" text with
    | Ok (m, _) -> print_endline (Sexp.of_module m)
    | Error d -> print_endline (Diagnostic.to_string d)
  in
  parse ~native:true "pub type View<T> = ?";
  parse ~native:false "pub type View<T> = ?";
  [%expect
    {|
    (module (pub (type View (T) ?)))
    t.lt:1:20: E0100: unexpected `?`: only the standard library declares a type without a representation; declare a record or a variant type
    |}];
  main "type Raw = ?\nfn f(r: Raw) {}\ntype Fine = { n: i64 }";
  [%expect {| main.lt:1: E0100 |}]

(* views.std-view: the tier of each module of the program. *)
let%expect_test "a module that names a view type is in the advanced tier" =
  match
    Driver.analyse
      (sources
         [
           ("main.lt", "use a\nfn main() { let n = a.f() }");
           ( "a.lt",
             "use std.view\npub fn f() -> i64 { view.Iter.of([1]).count() }" );
           ("b.lt", "use std.view\npub fn g() -> i64 { 1 }");
         ])
  with
  | [], Some (_, hir, _) ->
      List.iter
        (fun (m : Hir.module_) ->
          if not m.std then
            print_endline
              (m.name ^ ": "
              ^
              match m.tier with
              | Core -> "core"
              | Advanced -> "advanced"
              | Meta -> "meta"
              | Systems -> "systems"))
        hir;
      [%expect
        {|
        a: advanced
        b: core
        main: core
        |}]
  | _ -> print_endline "the program has errors"

(* views.viewable-types *)
let%expect_test "only strings and lists can be viewed" =
  main
    "use std.view\n\
     fn count<T>(v: view.View<T>) -> i64 { v.len() }\n\
     fn of<T>(x: T) -> i64 { view.View.all(x).len() }\n\
     fn f() -> i64 {\n\
     let make = view.View.all\n\
     let v: view.View<bool> = view.View.of(true, 0, 0)\n\
     view.View.all([1]).len() + make(1).len() + v.len()\n\
     }";
  [%expect
    {|
    main.lt:2: E0420
    main.lt:3: E0420
    main.lt:5: E0420
    main.lt:6: E0420
    main.lt:6: E0420
    |}]

(* views.view-types *)
let%expect_test "views can't be stored" =
  main
    "use std.view\n\
     type Keep = | Keep(Option<view.View<str>>)\n\
     const C: Option<view.View<str>> = None\n\
     fn take(f: fn(List<view.View<str>>) -> i64) {}\n\
     fn wrap<T>(x: T) -> List<T> { [x] }\n\
     fn f(s: str) -> i64 {\n\
     let v = view.View.all(s)\n\
     let g = || v.len()\n\
     let one = Some(v)\n\
     let r: Result<view.View<str>, str> = Ok(v)\n\
     let gs = [g]\n\
     let w = wrap(v)\n\
     let pairs = view.Iter.of([s]).map(|x| view.View.all(x)).enumerate(0)\n\
     let h = |xs: (view.View<str>, i64)| xs.1\n\
     gs.len() + w.len() + pairs.count()\n\
     }";
  [%expect
    {|
    main.lt:2: E0421
    main.lt:3: E0421
    main.lt:4: E0421
    main.lt:10: E0421
    main.lt:10: E0421
    main.lt:11: E0421
    main.lt:12: E0421
    main.lt:13: E0421
    main.lt:14: E0421
    |}]

(* views.across-calls and views.escaping; projections.results-that-write, for a view that reads an [inout]
   parameter *)
let%expect_test "a view leaves a function only through its result" =
  main
    "use std.view\n\
     fn of_let(s: str, t: str) -> view.View<str> {\n\
     if s.len() > 1 { return view.View.all(s) }\n\
     view.View.all(t).view(0, 0)\n\
     }\n\
     fn of_temporary() -> view.View<str> { view.View.all(\"ab\") }\n\
     fn branches(inout s: str, t: str) -> view.View<str> {\n\
     let local = \"x\"\n\
     if t.len() > 1 { view.View.all(s) } else { view.View.all(local) }\n\
     }\n\
     fn out(inout v: Option<view.View<str>>, s: str) { v = \
     Some(view.View.all(s)) }\n\
     fn kept(s: str) -> i64 {\n\
     let v = view.View.all(s)\n\
     view.Iter.of([1]).map(|x| x + v.len()).count()\n\
     }\n\
     fn inner(s: str) -> i64 {\n\
     let f = |x: str| view.View.all(x)\n\
     let g = || { let y = \"z\"\n\
     view.View.all(y) }\n\
     f(s).len() + g().len()\n\
     }";
  [%expect
    {|
    main.lt:6: E0422
    main.lt:9: E0428
    main.lt:9: E0422
    main.lt:11: E0422
    main.lt:14: E0422
    main.lt:19: E0422
    |}]

(* views.escaping: a view leaves no scope that binds one of its sources;
   projections.writable-bindings: the view given to a [var] binding writes. *)
let%expect_test "a view leaves no scope that binds a source" =
  main
    "use std.view\n\
     fn f(xs: List<str>, o: Option<str>, t: str) -> i64 {\n\
     let a = { let ys = [1]\n\
     view.View.all(ys) }\n\
     let b = if let Some(s) = o { view.View.all(s) } else { view.View.all(t) }\n\
     let c = match o { Some(s) => view.View.all(s).len(), None => 0 }\n\
     var w = view.View.all(xs)\n\
     for x in xs {\n\
     let zs = [x]\n\
     w = view.View.all(zs)\n\
     }\n\
     let d = { let g = { let ys = [2]\n\
     let v = view.View.all(ys)\n\
     || v.len() }\n\
     g() }\n\
     let e = if c > 0 { view.View.all(xs) } else { view.View.all(xs) }\n\
     a.len() + b.len() + w.len() + d + e.len()\n\
     }";
  [%expect
    {|
    main.lt:4: E0422
    main.lt:5: E0422
    main.lt:7: E0428
    main.lt:10: E0422
    main.lt:10: E0428
    main.lt:14: E0422
    |}]

(* views.reads-that-last, views.change-while-viewed and views.for-over-view; projections.writable-bindings, for the views given to [var]
   bindings *)
let%expect_test "a source can't change while a view reads it" =
  main
    "use std.view\n\
     fn grab(inout xs: List<i64>, n: i64) {}\n\
     fn f() {\n\
     var xs = [1, 2]\n\
     var ys = [3]\n\
     xs.push(view.View.all(xs).len())\n\
     grab(inout xs, view.View.all(xs).len())\n\
     let n = view.View.all(xs).len()\n\
     xs.push(n)\n\
     var v = view.View.all(xs)\n\
     ys.push(0)\n\
     v = view.View.all(ys)\n\
     ys.push(1)\n\
     let f = || v.len()\n\
     for x in view.Iter.of(xs) { xs.push(x) }\n\
     for x in xs { let w = view.View.all(xs)\n\
     xs.push(w.len()) }\n\
     }";
  [%expect
    {|
    main.lt:6: E0423
    main.lt:7: E0423
    main.lt:10: E0428
    main.lt:12: E0428
    main.lt:13: E0423
    main.lt:15: E0423
    main.lt:17: E0404
    |}]

(* views.what-view-is: a view only reads its source. *)
(* projections.writable-bindings and projections.places-through-views: an element of a [var] binding of a view type is
   a place, and the view given to the binding must write. *)
let%expect_test "a var binding of a view writes through it" =
  main
    "use std.view\n\
     fn bump(inout x: i64) {}\n\
     fn f() {\n\
     var v = view.View.all([1, 2])\n\
     v[0] = 3\n\
     bump(inout v[1])\n\
     v = view.View.all([4])\n\
     }";
  [%expect {|
    main.lt:4: E0428
    main.lt:7: E0428
    |}]

(* Runs the tests of the single-file program [text], printing what they
   print, then their verdicts. *)
let run text =
  match Driver.analyse (sources [ ("main.lt", text) ]) with
  | [], Some (env, hir, program) -> (
      match Eval.test ~out:stdout env hir program with
      | Ok verdicts ->
          List.iter
            (fun (v : Eval.verdict) -> Printf.printf "%d %b\n" v.line v.passed)
            verdicts
      | Error reason -> print_endline reason)
  | diagnostics, _ ->
      List.iter
        (fun (d : Diagnostic.t) ->
          Printf.printf "%d: %s\n" d.line (d.code :> string))
        diagnostics

(* views.laziness. [tens] divides by each element, so a test passes only if
   its iterator never asks for the element [0]. *)
let tens =
  "use std.view\n\
   fn tens(xs: List<i64>) -> view.Iter<i64> {\n\
   view.Iter.of(xs).map(|x| 10 / x)\n\
   }\n"

let%expect_test "an iterator asks for each element only when it is needed" =
  run
    (tens
   ^ "test \"made and adapted\" { let it = tens([0]).filter(|x| x > 0) }\n\
      test \"take\" { assert tens([1, 0]).take(1).count() == 1 }\n\
      test \"take_while\" {\n\
      assert tens([1, 0]).take_while(|x| x > 10).count() == 0\n\
      }\n\
      test \"map, then filter, per element\" {\n\
      assert tens([1, 0]).filter(|y| y == 10).first() == Some(10)\n\
      }\n\
      test \"zip ends with self\" {\n\
      assert view.range(0, 0).zip(tens([0])).count() == 0\n\
      }\n\
      test \"zip asks self first\" {\n\
      assert view.Iter.of([7]).zip(tens([1, 0])).count() == 1\n\
      }\n\
      test \"chain asks other last\" {\n\
      assert view.Iter.of([1]).chain(tens([0])).take(1).count() == 1\n\
      }\n\
      test \"skip asks and drops\" { assert tens([0, 1]).skip(1).count() == 1 }\n\
      test \"skip_while asks and drops\" {\n\
      assert tens([0, 1]).skip_while(|x| x > 5).count() == 1\n\
      }\n\
      test \"any stops\" { assert tens([1, 0]).any(|x| x == 10) }");
  [%expect
    {|
    5 true
    6 true
    7 true
    10 true
    13 true
    16 true
    19 true
    22 false
    23 false
    26 true
    |}]

(* views.for-over-view, views.laziness and views.consumers *)
let%expect_test "consumers read the elements in order, each from the first" =
  run
    (tens
   ^ "test \"each consumer starts over\" {\n\
      let it = view.Iter.of([1, 2]).enumerate(0)\n\
      assert it.count() == 2 && it.first() == Some((0, 1))\n\
      assert it.last() == Some((1, 2))\n\
      }\n\
      test \"a for loop runs its body before the next element\" {\n\
      for x in tens([1, 0]) { print(\"{x}\") }\n\
      }\n\
      test \"a consumer calls its callback in order\" {\n\
      let s = view.range(0, 3).fold(\"\", |s, x| {\n\
      print(\"{x}\")\n\
      \"{s}{x}\"\n\
      })\n\
      assert s == \"012\"\n\
      }\n\
      type Item = { key: i64, name: str }\n\
      impl Eq for Item {\n\
      fn eq(self, other: Item) -> bool { self.key == other.key }\n\
      }\n\
      impl Ord for Item {\n\
      fn compare(self, other: Item) -> Ordering { self.key.compare(other.key) }\n\
      }\n\
      test \"max and min keep the first of equal elements\" {\n\
      let items = [Item { key: 1, name: \"a\" }, Item { key: 1, name: \"b\" }]\n\
      let found = [view.Iter.of(items).max(), view.Iter.of(items).min()]\n\
      for i in found { if let Some(item) = i { assert item.name == \"a\" } }\n\
      }");
  [%expect
    {|
    10
    0
    1
    2
    5 true
    10 false
    13 true
    27 true
    |}]
