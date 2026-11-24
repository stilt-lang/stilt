(* Tests of the types a property may take (tests.generable-types): a type that holds
   infinitely many types is E0333, and one that holds finitely many is not.
   Each program has one property, and each test prints the errors. *)

open Diagnostics.Errors

let prop decls ty =
  main (decls ^ "\n/// prop: |x: " ^ ty ^ "| true\nfn f() {}\n")

let%expect_test "a type that grows through itself is E0333" =
  prop "type Grow<T> = | Stop | More(Grow<List<T>>)" "Grow<i64>";
  [%expect {| main.lt:2: E0333 |}];
  prop "type P<T> = | Z | S(P<(T, T)>)" "P<bool>";
  [%expect {| main.lt:2: E0333 |}]

let%expect_test "types that grow through each other are E0333" =
  prop
    "type Ping<T> = | End | Ping(Pong<List<T>>)\ntype Pong<T> = | Pong(Ping<T>)"
    "Pong<i64>";
  [%expect {| main.lt:3: E0333 |}]

let%expect_test "a type that holds a growing type is E0333" =
  prop
    "type Grow<T> = | Stop | More(Grow<List<T>>)\n\
     type Via<T> = { next: Option<Grow<T>> }"
    "List<Via<u8>>";
  [%expect {| main.lt:3: E0333 |}]

let%expect_test "a type that holds finitely many types is generable" =
  prop "type Bin<T> = | Leaf(T) | Node(Bin<T>, Bin<T>)" "Bin<str>";
  [%expect {| ok |}];
  prop "type A<T> = | X | Y(A<i64>)" "A<bool>";
  [%expect {| ok |}];
  prop "type Swap<T, U> = | Done | Next(Swap<U, T>)" "Swap<i64, str>";
  [%expect {| ok |}];
  prop "type Wrap<T> = | Wrap(List<T>)\ntype Outer<T> = | Outer(Wrap<List<T>>)"
    "Outer<u8>";
  [%expect {| ok |}]
