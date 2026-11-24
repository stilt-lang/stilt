(* Tests of trait parameters and constructor traits (traits.trait-parameters and traits.constructor-traits): the tier of a
   module (traits.advanced-tier), and the checks of bounds, member types, [where] clauses
   and kinds, each printing a program's errors as conformance.diagnostic-lines compares them. *)

open Stilt
open Diagnostics.Errors

let collection =
  "pub trait Collection<Item> {\n\
   fn at(self, i: i64) -> Option<Item>\n\
   }\n\
   impl<T> Collection<T> for List<T> {\n\
   fn at(self, i: i64) -> Option<T> { self.get(i) }\n\
   }\n"

(* traits.advanced-tier: declaring such a trait, naming it in a bound or writing
   a member type makes a module advanced; calling its methods doesn't. *)
let%expect_test "the tier of a module" =
  match
    Driver.analyse
      (Diagnostics.sources
         [
           ("main.lt", "use a\nfn main() { let n = [1].at(0) }");
           ("a.lt", collection);
           ("b.lt", "use a\npub fn f<C: a.Collection>(c: C) -> i64 { 0 }");
           ("c.lt", "trait Named { fn name(self) -> str }");
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
        b: advanced
        c: core
        main: core
        |}]
  | _ -> print_endline "the program has errors"

(* traits.bound-arguments: a bound's argument may be another generic, which the impl
   gives; one that the impl doesn't give is E0318. *)
let%expect_test "a bound's arguments come from the impl" =
  main
    (collection
   ^ "fn first<C: Collection<T>, T: Show>(c: C) -> str {\n\
      match c.at(0) { Some(x) => \"{x}\", None => \"\" }\n\
      }\n\
      fn f() -> str { first([1]) }\n\
      fn sum<C: Collection<i64>>(c: C) -> i64 { 0 }\n\
      fn g() -> i64 { sum([\"a\"]) }");
  [%expect {| main.lt:12: E0318 |}]

(* traits.member-types and traits.where *)
let%expect_test "member types and where clauses" =
  main
    (collection
   ^ "fn biggest<C: Collection>(c: C) -> Option<C.Item> where C.Item: Ord {\n\
      let a = c.at(0)\n\
      let b: Option<C.Item> = c.at(1)\n\
      if a > b { a } else { b }\n\
      }\n\
      fn worse<C: Collection>(c: C) -> bool {\n\
      c.at(0) < c.at(1)\n\
      }");
  [%expect {| main.lt:13: E0318 |}];
  main
    (collection
   ^ "fn h<C: Collection<i64>>(c: C) -> C.Item { 0 }\n\
      fn k<T>(t: T) where T: Show {}");
  [%expect {| main.lt:8: E0336 |}];
  (* A bound's argument fixes the member type of an impl, which must meet the
     clause's bound. *)
  main
    (collection
   ^ "type Bin<C> = { c: C }\n\
      impl<C: Collection<f64>> Show for Bin<C> where C.Item: Hash {\n\
      fn show(self) -> str { \"\" }\n\
      }\n\
      impl<C: Collection<str>> Bin<C> where C.Item: Hash {}");
  [%expect {| main.lt:8: E0318 |}]

(* traits.constructor-traits, traits.constructor-impls and traits.constructor-parameters *)
let%expect_test "constructors take their arity" =
  main
    "trait Mappable {\n\
     fn transform<A, B>(self: Self<A>, f: fn(A) -> B) -> Self<B>\n\
     }\n\
     impl<T> Mappable for List {}\n\
     impl Mappable for Option {\n\
     fn transform<A, B>(self: Option<A>, f: fn(A) -> B) -> Option<B> { None }\n\
     }\n\
     type Box<F> = { f: F }\n\
     impl<F: Mappable> Show for Box<F> { fn show(self) -> str { \"\" } }\n\
     fn id<F: Mappable>(xs: F<str>) -> F<str> { xs.transform(|s| s) }\n\
     fn f() -> Option<str> { id(Some(\"a\")) }\n\
     fn g(x: (i64, str)) -> i64 { id(x) }\n\
     fn h(x: i64) -> i64 { id(x) }";
  [%expect
    {|
    main.lt:4: E0337
    main.lt:9: E0337
    main.lt:12: E0318
    main.lt:13: E0311
    main.lt:13: E0311
    |}]

(* traits.constructor-parameters, and effects.non-escaping-parameters: a constructor trait's non-escaping
   parameter passes its argument's effects through, and phase 2 checks the
   bodies that call through a bound. *)
let%expect_test "effects pass through, and phase 2 runs" =
  main
    "type Odd = | Odd(i64)\n\
     trait Mappable {\n\
     fn transform<A, B>(self: Self<A>, f: fn(A) -> B) -> Self<B>\n\
     }\n\
     fn halve(x: i64) -> i64 / raise<Odd> { if x % 2 == 0 { x / 2 } else { \
     raise Odd(x) } }\n\
     fn halved<F: Mappable>(xs: F<i64>) -> F<i64> { try xs.transform(halve) }\n\
     fn grow<F: Mappable>(xs: F<i64>) -> F<i64> {\n\
     var ys = [1]\n\
     for y in ys { ys.push(y) }\n\
     xs.transform(|x| x)\n\
     }";
  [%expect {|
    main.lt:6: E0502
    main.lt:9: E0404
    |}]
