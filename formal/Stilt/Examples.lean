import Stilt.Exclusivity
import Stilt.Semantics

/-!
# Examples

Runs of small programs, which check the evaluator against the required tests
of values.value-semantics, expressions.statements, effects.rows, traits.methods and modes.law. Each expected outcome comes from
the rule cited, and each holds in both models of memory. `main` returns `()`
(program.main), so each program raises the value it shows, as a run shows
an error that escapes `main` (program.exit-statuses).
-/

namespace Stilt.Examples

/-- A program from its functions, the type of the value it shows, its records
and `main`, whose row is `raise<shown>`. The examples run programs without
typing them. -/
private def program (fns : List FnDecl) (shown : Ty) (main : Expr)
    (records : List RecordDecl := []) (impls : List ImplDecl := []) : Program :=
  ⟨⟨records, [], fns, impls, [], [], []⟩, main, ⟨false, some shown, [], [], none⟩⟩

/-- A call of a function declared at the top level. -/
private def call (f : Name) (args : List Arg) (result : Ty :=
  .unit) : Expr := .call (.fnRef f [] []) args result

private def place (x : Name) (path : List Projection := []) : Place := ⟨x, path⟩

private def ints (ns : List Int) : Value := .list (ns.map .int)

private def listOf (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-- `xs[0]`, as a place. -/
private def first (xs : Name) : Place := ⟨xs, [.index (.int 0)]⟩

/-- A parameter, of type `i64` unless another is given. -/
private def param (mode : Mode) (x : Name) (type : Ty := .i64) : Param := ⟨mode, x, type, none⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-! ## values.independent-copies: copies are independent -/

/-- `var a = [1]; let b = a; a[0] = 2; raise b` raises `[1]`. -/
example : agree (program [] (.list .i64)
    (.varIn "a" (.list .i64) (listOf [1])
      (.letIn "b" (.list .i64) (.var "a")
        (.seq (.assign (first "a") (.int 2)) (.raise (.var "b"))))))
    (.raised (ints [1])) := ⟨rfl, rfl⟩

/-- A closure captures a copy when it is created (expressions.capture):
`var x = 1; let f = || x; x = 2; raise f()` raises `1`. -/
example : agree (program [] .i64
    (.varIn "x" .i64 (.int 1)
      (.letIn "f" (.fn [] .i64 Row.pure) (.closure [] .i64 Row.pure (.var "x"))
        (.seq (.assign (place "x") (.int 2)) (.raise (.call (.var "f") [] .i64))))))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-! ## values.inout-arguments: an `inout` argument keeps the callee's changes -/

/-- `fn fill(inout xs: List<i64>) / raise<i64> { xs[0] = 7; raise 1 }`. -/
private def fill : FnDecl :=
  ⟨"fill", [], [], [param .inout "xs" (.list .i64)], .unit, ⟨false, some .i64, [], [], none⟩,
    .seq (.assign (first "xs") (.int 7)) (.raise (.int 1))⟩

/-- After a raise: `var xs = [0]; try fill(inout xs) catch e => (); raise xs`
raises `[7]`. -/
example : agree (program [fill] (.list .i64)
    (.varIn "xs" (.list .i64) (listOf [0])
      (.seq (.tryCatch (call "fill" [.inout (place "xs")]) .i64 "e" .unit .unit)
        (.raise (.var "xs")))))
    (.raised (ints [7])) := ⟨rfl, rfl⟩

/-- A closure's `inout` parameter keeps the changes too (expressions.inout-closure-parameters):
`var n = 0; let f = |inout m: i64| { m = 5; raise 1 }; try f(inout n) catch e
=> (); raise n` raises `5`. -/
example : agree (program [] .i64
    (.varIn "n" .i64 (.int 0)
      (.letIn "f" (.fn [(.inout, .i64)] .unit ⟨false, some .i64, [], [], none⟩)
        (.closure [param .inout "m"] .unit ⟨false, some .i64, [], [], none⟩
          (.seq (.assign (place "m") (.int 5)) (.raise (.int 1))))
        (.seq (.tryCatch (.call (.var "f") [.inout (place "n")] .i64) .i64 "e" .unit .unit)
          (.raise (.var "n"))))))
    (.raised (.int 5)) := ⟨rfl, rfl⟩

/-- `fn bump(inout n: i64) { n = 5 }`. -/
private def bump : FnDecl :=
  ⟨"bump", [], [], [param .inout "n"], .unit, Row.pure, .assign (place "n") (.int 5)⟩

/-- After a return, through an element: `var xs = [1, 2]; bump(inout xs[1]);
raise xs` raises `[1, 5]`. -/
example : agree (program [bump] (.list .i64)
    (.varIn "xs" (.list .i64) (listOf [1, 2])
      (.seq (call "bump" [.inout (place "xs" [.index (.int 1)])]) (.raise (.var "xs")))))
    (.raised (ints [1, 5])) := ⟨rfl, rfl⟩

/-! ## values.inout-argument-order: the order of `inout` arguments -/

/-- `fn after(inout slot: i64, n: i64) -> i64 { slot }`. -/
private def after : FnDecl :=
  ⟨"after", [], [], [param .inout "slot", param .let "n"], .i64, Row.pure, .var "slot"⟩

/-- `fn set(inout x: i64) -> i64 { x = 9; 0 }`. -/
private def set : FnDecl :=
  ⟨"set", [], [], [param .inout "x"], .i64, Row.pure,
    .seq (.assign (place "x") (.int 9)) (.int 0)⟩

/-- A later argument changes the place, and the callee sees the change:
`var a = 1; raise after(inout a, set(inout a))` raises `9`. -/
example : agree (program [after, set] .i64
    (.varIn "a" .i64 (.int 1)
      (.raise (call "after" [.inout (place "a"), .value (call "set" [.inout (place "a")])]))))
    (.raised (.int 9)) := ⟨rfl, rfl⟩

/-- An `inout` argument out of bounds panics when the call starts, after
every argument: `var xs = [0]; raise after(inout xs[5], 1)` panics with the
kind `bounds`. -/
example : agree (program [after] .i64
    (.varIn "xs" (.list .i64) (listOf [0])
      (.raise (call "after" [.inout (place "xs" [.index (.int 5)]), .value (.int 1)]))))
    (.panicked .bounds) := ⟨rfl, rfl⟩

/-- If a later argument raises, the call never starts and the place is never
read: `raise (try after(inout xs[5], raise 3) catch e => e)` raises `3`. -/
example : agree (program [after] .i64
    (.varIn "xs" (.list .i64) (listOf [0])
      (.raise (.tryCatch
        (call "after" [.inout (place "xs" [.index (.int 5)]), .value (.raise (.int 3))])
        .i64 "e" (.var "e") .i64))))
    (.raised (.int 3)) := ⟨rfl, rfl⟩

/-- `type P = { x: i64, y: i64 }`. -/
private def pointType : RecordDecl := ⟨"P", [("x", .i64), ("y", .i64)]⟩

/-- `fn swap(inout a: i64, inout b: i64) { let t = a; a = b; b = t }`. -/
private def swap : FnDecl :=
  ⟨"swap", [], [], [param .inout "a", param .inout "b"], .unit, Row.pure,
    .letIn "t" .i64 (.var "a")
      (.seq (.assign (place "a") (.var "b")) (.assign (place "b") (.var "t")))⟩

/-- The write-back of two `inout` arguments, from a record literal written in
another order than its fields are declared: `var p = P { y: 2, x: 1 };
swap(inout p.x, inout p.y); raise p` raises `P { x: 2, y: 1 }`. -/
example : agree (program [swap] (.record "P") (records := [pointType])
    (.varIn "p" (.record "P") (.record "P" [("y", .int 2), ("x", .int 1)])
      (.seq (call "swap" [.inout (place "p" [.field "x"]), .inout (place "p" [.field "y"])])
        (.raise (.var "p")))))
    (.raised (.record "P" [("x", .int 2), ("y", .int 1)])) := ⟨rfl, rfl⟩

/-- A record literal evaluates its fields in the order they are written:
`let p = P { y: raise 1, x: raise 2 }` raises `1`. -/
example : agree (program [] .i64 (records := [pointType])
    (.letIn "p" (.record "P") (.record "P" [("y", .raise (.int 1)), ("x", .raise (.int 2))])
      .unit))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-! ## effects.innermost-catch: the innermost `catch` handles a raise -/

/-- `raise (try (try raise 1 catch e => raise 2) catch e => e)` raises `2`. -/
example : agree (program [] .i64
    (.raise (.tryCatch (.tryCatch (.raise (.int 1)) .i64 "e" (.raise (.int 2)) .i64)
      .i64 "e" (.var "e") .i64)))
    (.raised (.int 2)) := ⟨rfl, rfl⟩

/-- `raise (try (try raise 1 catch e => e) catch e => 0)` raises `1`. -/
example : agree (program [] .i64
    (.raise (.tryCatch (.tryCatch (.raise (.int 1)) .i64 "e" (.var "e") .i64)
      .i64 "e" (.int 0) .i64)))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-! ## expressions.for-iterables: a `for` loop -/

/-- `var last = 0; for x in [1, 2, 3] { last = x }; raise last` raises `3`. -/
example : agree (program [] .i64
    (.varIn "last" .i64 (.int 0)
      (.seq (.for "x" .i64 (listOf [1, 2, 3]) (.assign (place "last") (.var "x")))
        (.raise (.var "last")))))
    (.raised (.int 3)) := ⟨rfl, rfl⟩

/-! ## modes.overlapping-inout: other arguments are read before the call -/

/-- `fn keep(inout a: i64, n: i64) -> i64 { a = 5; n }`. -/
private def keep : FnDecl :=
  ⟨"keep", [], [], [param .inout "a", param .let "n"], .i64, Row.pure,
    .seq (.assign (place "a") (.int 5)) (.var "n")⟩

/-- `keep(inout a, a)` passes the value `a` had before the call: `var a = 1;
raise [keep(inout a, a), a]` raises `[1, 5]`. -/
example : agree (program [keep] (.list .i64)
    (.varIn "a" .i64 (.int 1)
      (.raise (.list .i64 [call "keep" [.inout (place "a"), .value (.var "a")], .var "a"]))))
    (.raised (ints [1, 5])) := ⟨rfl, rfl⟩

/-! ## traits.methods: methods and their receivers -/

/-- `self`, as a place. -/
private def this (path : List Projection := []) : Place := ⟨selfName, path⟩

/-- `recv.m(args)`, for a method of `T` with no row variables. -/
private def send (T m : Name) (recv : Arg) (args : List Arg) (result : Ty := .unit) : Expr :=
  Expr.methodCall T m [] recv args result

/-- `type Counter = { n: i64 }`. -/
private def counterType : RecordDecl := ⟨"Counter", [("n", .i64)]⟩

/-- `fn bumped(self) -> Counter { var c = self; c.n = 5; c }`: it changes its
copy of the receiver, rebound with `var` (modes.what-can-be-modified). -/
private def bumped : FnDecl :=
  ⟨"bumped", [], [], [param .let selfName (.record "Counter")], .record "Counter", Row.pure,
    .varIn "c" (.record "Counter") (.var selfName)
      (.seq (.assign (place "c" [.field "n"]) (.int 5)) (.var "c"))⟩

/-- `fn add(inout self) / raise<i64> { self.n = 7; raise 1 }`. -/
private def add : FnDecl :=
  ⟨"add", [], [], [param .inout selfName (.record "Counter")], .unit, ⟨false, some .i64, [], [], none⟩,
    .seq (.assign (this [.field "n"]) (.int 7)) (.raise (.int 1))⟩

/-- `fn get(inout self, n: i64) -> i64 { self.n }`. -/
private def get : FnDecl :=
  ⟨"get", [], [], [param .inout selfName (.record "Counter"), param .let "n"], .i64, Row.pure,
    .field (.var selfName) "n"⟩

/-- `fn reset(inout self) -> i64 { self.n = 9; 0 }`. -/
private def reset : FnDecl :=
  ⟨"reset", [], [], [param .inout selfName (.record "Counter")], .i64, Row.pure,
    .seq (.assign (this [.field "n"]) (.int 9)) (.int 0)⟩

/-- `fn swap(inout self, inout other: Counter) { let t = self; self = other;
other = t }`. -/
private def swapWith : FnDecl :=
  ⟨"swap", [], [],
    [param .inout selfName (.record "Counter"), param .inout "other" (.record "Counter")],
    .unit, Row.pure,
    .letIn "t" (.record "Counter") (.var selfName)
      (.seq (.assign (this) (.var "other")) (.assign (place "other") (.var "t")))⟩

/-- `impl Counter { … }`. -/
private def counterImpl : ImplDecl := ⟨"Counter", [bumped, add, get, reset, swapWith]⟩

/-- `Counter { n: k }`. -/
private def counter (k : Int) : Expr := .record "Counter" [("n", .int k)]

private def counterValue (k : Int) : Value := .record "Counter" [("n", .int k)]

/-- A receiver taken by `self` is an independent copy (values.passing-values):
`let c = Counter { n: 1 }; let d = c.bumped(); raise [c.n, d.n]` raises
`[1, 5]`. -/
example : agree (program [] (.list .i64) (records := [counterType]) (impls := [counterImpl])
    (.letIn "c" (.record "Counter") (counter 1)
      (.letIn "d" (.record "Counter") (send "Counter" "bumped" (.value (.var "c")) [] (.record "Counter"))
        (.raise (.list .i64 [.field (.var "c") "n", .field (.var "d") "n"])))))
    (.raised (ints [1, 5])) := ⟨rfl, rfl⟩

/-- An `inout self` receiver keeps the callee's changes after a raise
(values.inout-arguments): `var c = Counter { n: 1 }; try c.add() catch e => ();
raise c.n` raises `7`. -/
example : agree (program [] .i64 (records := [counterType]) (impls := [counterImpl])
    (.varIn "c" (.record "Counter") (counter 1)
      (.seq (.tryCatch (send "Counter" "add" (.inout (place "c")) []) .i64 "e" .unit .unit)
        (.raise (.field (.var "c") "n")))))
    (.raised (.int 7)) := ⟨rfl, rfl⟩

/-- The receiver is evaluated first, its indexes included (values.left-to-right;
modes.durations): `var cs = [Counter { n: 0 }]; cs[raise 1].get(raise 2)`
raises `1`. -/
example : agree (program [] .i64 (records := [counterType]) (impls := [counterImpl])
    (.varIn "cs" (.list (.record "Counter")) (.list (.record "Counter") [counter 0])
      (send "Counter" "get" (.inout (place "cs" [.index (.raise (.int 1))]))
        [.value (.raise (.int 2))] .i64)))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-- The receiver's place is read when the call starts, so a change that a
later argument makes to it reaches the callee, as in `xs.push(xs.pop() else
0)` (values.left-to-right): `var c = Counter { n: 1 }; raise c.get(c.reset())`
raises `9`. -/
example : agree (program [] .i64 (records := [counterType]) (impls := [counterImpl])
    (.varIn "c" (.record "Counter") (counter 1)
      (.raise (send "Counter" "get" (.inout (place "c"))
        [.value (send "Counter" "reset" (.inout (place "c")) [] .i64)] .i64))))
    (.raised (.int 9)) := ⟨rfl, rfl⟩

/-- `type Pair = { x: Counter, y: Counter }`. -/
private def pairType : RecordDecl :=
  ⟨"Pair", [("x", .record "Counter"), ("y", .record "Counter")]⟩

/-- The write-back of a receiver and an `inout` argument: `var p = Pair { x:
Counter { n: 1 }, y: Counter { n: 2 } }; p.x.swap(inout p.y); raise p` raises
`Pair { x: Counter { n: 2 }, y: Counter { n: 1 } }`. -/
example : agree (program [] (.record "Pair") (records := [counterType, pairType])
    (impls := [counterImpl])
    (.varIn "p" (.record "Pair") (.record "Pair" [("x", counter 1), ("y", counter 2)])
      (.seq (send "Counter" "swap" (.inout (place "p" [.field "x"]))
          [.inout (place "p" [.field "y"])])
        (.raise (.var "p")))))
    (.raised (.record "Pair" [("x", counterValue 2), ("y", counterValue 1)])) := ⟨rfl, rfl⟩

end Stilt.Examples
