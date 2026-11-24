import Stilt.Panics.Theorem

/-!
# Code with and without panics

Which code `without panic` accepts (effects.panicking-operations): `n / 2`,
whose divisor is written as a literal other than zero, and `n / d` where a test
guards `d` (facts.divisors), `when c { x / 2 }`, `if d != 0 { n / d }` and `if d == 0 { 0 } else
{ n / d }`, and `for d in 1..4 { n / d }`, whose variable is known positive
(facts.known-signs), but neither `n / d` alone, nor `for d in 0..4 { n / d }`, nor `n / 0`, nor an index, nor a guarded
division after `d = 0`. A program that divides by a variable holding zero
panics with `divide-by-zero`, which the check rules out, and a panic-free
program may still overflow, which `without panic` doesn't rule out
(effects.without-overflow), as `Program.PanicFree.runCopy` allows.
-/

namespace Stilt.Examples.Panics

/-- `a / b` on `i64`s. -/
private def div (a b : Expr) : Expr := .op (.arith .div .i64) [a, b]

private def program (main : Expr) : Program := ⟨⟨[], [], [], [], [], [], []⟩, main, Row.pure⟩

example : (div (.var "n") (.int 2)).panicFree = true := rfl
example : (div (.var "n") (.var "d")).panicFree = false := rfl
example : (div (.var "n") (.int 0)).panicFree = false := rfl
example : (Expr.index (.var "xs") (.int 0)).panicFree = false := rfl
example : (Expr.op (.list .slice) [.var "xs", .int 0, .int 1]).panicFree = false := rfl
example : (Expr.op (.list .push) [.var "xs", .int 0]).panicFree = true := rfl

/-- `d != 0`, `d == 0` and `0 < d` on `i64`s. -/
private def test (c : Cmp) (l r : Expr) : Expr := .op (.compare c .i64) [l, r]

/-- `when c { x / 2 }` adds only `deadlock` (shared.when-on-value-already-held), but a fact
about `x` outside it says nothing of the name `x` inside it. -/
example : (Expr.held [("x", .i64)] [.var "c"] (div (.var "x") (.int 2))).panicFree = true := rfl
example : (Expr.if (test .ne (.var "x") (.int 0)) .i64
    (.held [("x", .i64)] [.var "c"] (div (.var "n") (.var "x"))) (.int 0)).panicFree = false := rfl

example : (Expr.if (test .ne (.var "d") (.int 0)) .i64 (div (.var "n") (.var "d")) (.int 0)).panicFree = true := rfl
example : (Expr.if (test .eq (.var "d") (.int 0)) .i64 (.int 0) (div (.var "n") (.var "d"))).panicFree = true := rfl
example : (Expr.if (test .lt (.int 0) (.var "d")) .i64 (div (.var "n") (.var "d")) (.int 0)).panicFree = true := rfl
example : (Expr.if (test .eq (.var "d") (.int 0)) .i64 (div (.var "n") (.var "d")) (.int 0)).panicFree = false := rfl
example : (Expr.if (test .ne (.var "d") (.int 0)) .i64
    (.seq (.assign ⟨"d", []⟩ (.int 0)) (div (.var "n") (.var "d"))) (.int 0)).panicFree = false := rfl
example : (Expr.if (test .ne (.var "d") (.int 0)) .i64
    (.letIn "d" .i64 (.int 0) (div (.var "n") (.var "d"))) (.int 0)).panicFree = false := rfl

/-- `d != 0 && n / d > 1` and `d == 0 || n / d > 1`, as the calculus writes `&&` and
`||`: the left operand gives its facts to the right one (facts.guarding-tests). -/
private def gt1 : Expr := test .gt (div (.var "n") (.var "d")) (.int 1)

example : (Expr.if (test .ne (.var "d") (.int 0)) .bool gt1 (.bool false)).panicFree = true := rfl
example : (Expr.if (test .eq (.var "d") (.int 0)) .bool (.bool true) gt1).panicFree = true := rfl
example : (Expr.if (test .eq (.var "d") (.int 0)) .bool gt1 (.bool false)).panicFree = false := rfl

/-- `if d != 0 && e != 0 { n / d / e }`, `if !(d == 0) { n / d }`, and the code after
`if d == 0 || e == 0 { return 0 }`: a condition gives each conjunct of its `&&` chain,
read through `!`, and its negation each disjunct's negation of its `||` chain
(facts.guarding-tests). -/
private def both (c : Expr) : Expr := .if c .i64 (div (div (.var "n") (.var "d")) (.var "e")) (.int 0)
private def ne0 (x : Name) : Expr := test .ne (.var x) (.int 0)
private def eq0 (x : Name) : Expr := test .eq (.var x) (.int 0)

example : (both (.if (ne0 "d") .bool (ne0 "e") (.bool false))).panicFree = true := rfl
example : (both (.if (ne0 "d") .bool (ne0 "e") (.bool true))).panicFree = false := rfl
example : (Expr.if (.op .not [eq0 "d"]) .i64 (div (.var "n") (.var "d")) (.int 0)).panicFree = true := rfl
example : (Expr.seq (.if (.if (eq0 "d") .bool (.bool true) (eq0 "e")) .unit (.return (.int 0)) .unit)
    (div (div (.var "n") (.var "d")) (.var "e"))).panicFree = true := rfl

/-- `if d == 0 { return 0 }; n / d`: the code after an `if` whose then-branch
returns counts on the negation of its test; not when the then-branch may end. -/
private def early (jump : Expr) : Expr :=
  .seq (.if (test .eq (.var "d") (.int 0)) .unit jump .unit) (div (.var "n") (.var "d"))

example : (early (.return (.int 0))).panicFree = true := rfl
example : (early (.seq (.int 1) .break)).panicFree = true := rfl
example : (early (.int 0)).panicFree = false := rfl
/-- Each path of the then-branch jumps, through an `if`, a `let` and a `match`; not when
one path of the `if` or one arm of the `match` ends. -/
example : (early (.if (.var "b") .unit (.return (.int 0)) (.raise (.int 1)))).panicFree = true := rfl
example : (early (.letIn "y" .i64 (.int 1) (.return (.var "y")))).panicFree = true := rfl
example : (early (.if (.var "b") .unit (.return (.int 0)) .unit)).panicFree = false := rfl
example : (early (.match (.var "b") .unit [⟨.int 0, [], .return (.int 0)⟩, ⟨.wild, [], .break⟩])).panicFree =
    true := rfl
example : (early (.match (.var "b") .unit [⟨.int 0, [], .return (.int 0)⟩, ⟨.wild, [], .unit⟩])).panicFree =
    false := rfl

/-- `for d in a..4 { n / d }`. -/
private def overRange (a : Int) : Expr :=
  .for "d" .i64 (.op (.list (.range false)) [.int a, .int 4]) (div (.var "n") (.var "d"))

example : (overRange 1).panicFree = true := rfl
example : (overRange 0).panicFree = false := rfl

/-- `if i >= 0 && i < xs.len() { xs[i] } else { 0 }` reads within the list's bounds
(facts.guards); a test of one bound only doesn't prove the index. -/
private def len (xs : Name) : Expr := .op (.list .len) [.var xs]
private def at_ : Expr := .index (.var "xs") (.var "i")

example : (Expr.if (.if (test .ge (.var "i") (.int 0)) .bool (test .lt (.var "i") (len "xs")) (.bool false))
    .i64 at_ (.int 0)).panicFree = true := rfl
example : (Expr.if (test .lt (.var "i") (len "xs")) .i64 at_ (.int 0)).panicFree = false := rfl
example : (Expr.if (test .ge (.var "i") (.int 0)) .i64 at_ (.int 0)).panicFree = false := rfl

/-- `for i in a..xs.len() { xs[i] }` reads within the bounds of `xs` when `a` isn't
negative (facts.range-loops); not up to `xs.len()` included, nor when the body
writes `xs`. -/
private def overList (a : Int) (inclusive : Bool) (body : Expr) : Expr :=
  .for "i" .i64 (.op (.list (.range inclusive)) [.int a, len "xs"]) body

example : (overList 0 false at_).panicFree = true := rfl
example : (overList 1 false at_).panicFree = true := rfl
example : (overList (-1) false at_).panicFree = false := rfl
example : (overList 0 true at_).panicFree = false := rfl
example : (overList 0 false (.seq (.assign ⟨"xs", []⟩ (.list .i64 [])) at_)).panicFree = false := rfl

/-- `if a >= 0 { for i in a..xs.len() { xs[i] } }`: a range from a variable known not
negative proves the index (facts.range-loops); not without the test. -/
private def fromVar : Expr := .for "i" .i64 (.op (.list (.range false)) [.var "a", len "xs"]) at_

example : (Expr.if (test .ge (.var "a") (.int 0)) .unit fromVar .unit).panicFree = true := rfl
example : fromVar.panicFree = false := rfl

/-- `for i in a..xs.len() - c { xs[i + k] }` and `for i in a..xs.len() { xs[i - k] }`:
an offset reads within the bounds of `xs` when `c` is at least `k`, and when `a` is
(facts.range-loops); not otherwise, nor when `k` is a variable. -/
private def lit (o : Arith) (j : Name) (k : Int) : Expr := .op (.arith o .i64) [.var j, .int k]
private def upTo (a c : Int) (body : Expr) : Expr :=
  .for "i" .i64 (.op (.list (.range false)) [.int a, .op (.arith .sub .i64) [len "xs", .int c]]) body
private def atOffset (o : Arith) (k : Int) : Expr := .index (.var "xs") (lit o "i" k)

example : (upTo 0 1 (atOffset .add 1)).panicFree = true := rfl
example : (upTo 0 2 (atOffset .add 1)).panicFree = true := rfl
example : (upTo 0 1 (atOffset .add 2)).panicFree = false := rfl
example : (overList 0 false (atOffset .add 1)).panicFree = false := rfl
example : (overList 1 false (atOffset .sub 1)).panicFree = true := rfl
example : (overList 2 false (atOffset .sub 1)).panicFree = true := rfl
example : (overList 0 false (atOffset .sub 1)).panicFree = false := rfl
example : (upTo 0 1 (.index (.var "xs") (.op (.arith .add .i64) [.var "i", .var "k"]))).panicFree = false :=
  rfl

/-- `for i in 0..xs.len() { xs[i] = xs[i] * 2 }` and `xs[i] = 0; xs[i]`: a store into
an element at a proved index keeps the list's length, so the loop still proves the
index after it; not a store of the whole list, nor one at `i + 1`, nor one whose value
stores the list whole first. -/
private def store (k : Expr) (v : Expr) : Expr := .assign ⟨"xs", [.index k]⟩ v

example : (overList 0 false (store (.var "i") (.op (.arith .mul .i64) [at_, .int 2]))).panicFree = true := rfl
example : (overList 0 false (.seq (store (.var "i") (.int 0)) at_)).panicFree = true := rfl
example : (overList 0 false (store (lit .add "i" 1) (.int 0))).panicFree = false := rfl
example : (overList 0 false (store (.var "i") (.seq (.assign ⟨"xs", []⟩ (.list .i64 [])) (.int 0)))).panicFree =
    false := rfl

/-- `if m.contains(k) { m[k] } else { 0 }` reads a key the map has (facts.keys), and
so does the else-branch of `!m.contains(1)`; a test of another key, or a write
of the map in between, doesn't prove it. -/
private def contains (k : Expr) : Expr := .op (.map .contains) [.var "m", k]
private def get (k : Expr) : Expr := .op (.map .index) [.var "m", k]

example : (Expr.if (contains (.var "k")) .i64 (get (.var "k")) (.int 0)).panicFree = true := rfl
example : (Expr.if (.op .not [contains (.int 1)]) .i64 (.int 0) (get (.int 1))).panicFree = true := rfl
example : (Expr.if (contains (.var "j")) .i64 (get (.var "k")) (.int 0)).panicFree = false := rfl
example : (Expr.if (contains (.var "k")) .i64
    (.seq (.assign ⟨"m", []⟩ (.op (.map .remove) [.var "m", .var "k"])) (get (.var "k"))) (.int 0)).panicFree =
    false := rfl
example : (get (.var "k")).panicFree = false := rfl

/-- `let d = 0; 1 / d` divides by zero, and the check rejects it. -/
private def byZero : Program := program (.letIn "d" .i64 (.int 0) (div (.int 1) (.var "d")))

example : ¬byZero.PanicFree := fun h => nomatch h.2
example : (byZero.runCopy 8).observe = .panicked .divideByZero := rfl

/-- `127 + 1` on `i8` holds no site of `panic`, and overflows. -/
private def overflows : Program := program (.op (.arith .add .i8) [.int 127, .int 1])

example : overflows.PanicFree := ⟨(fun _ h => nomatch h), rfl⟩
example : (overflows.runCopy 8).observe = .panicked .overflow := rfl

end Stilt.Examples.Panics
