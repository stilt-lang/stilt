import Stilt.Ends.Theorem

/-!
# Code that ends

Which code `without div` accepts (facts.div): `quad(n)`, which calls `double`
twice, inside a `for` loop over a list. The check accepts it, and it ends at
the fuel that the program's text bounds, 10, whatever the number of turns, and
not at 9. It rejects `f(n) = f(n)`, recursion that no ranking bounds, which
runs out of the fuel it is given. It accepts a `while` that counts toward its
bound (facts.counting-loops), which needs a fuel more for each turn, and
rejects one whose step is missing, conditional, after a `continue`, zero or
away from the bound, or whose body writes what the bound reads.
-/

namespace Stilt.Examples.Ends

/-- `a + b` on `i64`s. -/
private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]

private def fn (name : Name) (body : Expr) : FnDecl :=
  ⟨name, [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure, body, {}⟩

private def call (f : Name) (e : Expr) (result : Ty :=
  .i64) : Expr := .call (.fnRef f [] []) [.value e] result

/-- `fn double(n: i64) -> i64 { n + n }` and `fn quad(n: i64) -> i64 { double(double(n)) }`. -/
private def decls : Decls :=
  ⟨[], [], [fn "double" (add (.var "n") (.var "n")), fn "quad" (call "double" (call "double" (.var "n")))],
    [], [], [], []⟩

/-- `var s = 0; for x in [1, 2, 3] { s = s + quad(x) }; raise s`. -/
private def summed : Program :=
  ⟨decls, .varIn "s" .i64 (.int 0) (.seq
    (.for "x" .i64 (.list .i64 [.int 1, .int 2, .int 3])
      (.assign ⟨"s", []⟩ (add (.var "s") (call "quad" (.var "x")))))
    (.raise (.var "s"))), ⟨false, some .i64, [], [], none⟩, {}⟩

example : summed.divFree = true := rfl
example : summed.DivFree := Program.divFree_spec rfl
example : summed.main.needs summed.decls.rank = 10 := rfl
example : (summed.runCopy 10).observe = .raised (.int 24) := rfl
example : (summed.runCopy 9).observe = .outOfFuel := rfl

/-- `fn f(n: i64) -> i64 { f(n) }`. -/
private def forever : Program :=
  ⟨⟨[], [], [fn "f" (call "f" (.var "n"))], [], [], [], []⟩, call "f" (.int 0), ⟨false, some .i64, [], [], none⟩, {}⟩

example : forever.divFree = false := rfl
example : (forever.runCopy 12).observe = .outOfFuel := rfl

example : (Expr.while (.bool true) .unit).divFree Limited.all = false := rfl
/-- `when c { x }` adds no `div` (shared.when). -/
example : (Expr.held [("x", .i64)] [.var "c"] (.var "x")).divFree Limited.all = true := rfl

private def lt (a b : Expr) : Expr := .op (.compare .lt .i64) [a, b]
private def step (x : Name) (o : Arith) (k : Int) : Expr := .assign ⟨x, []⟩ (.op (.arith o .i64) [.var x, .int k])

/-- `var i = 0; var s = 0; while i < n { s = s + i; i = i + 1 }; raise s`, with `n` given:
with `n = 10` it ends at fuel 18 and not 17, and with `n = 20` it needs more, as each
turn costs a fuel. -/
private def counted (n : Int) (cond : Expr) (body : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], []⟩, .letIn "n" .i64 (.int n) (.varIn "i" .i64 (.int 0) (.varIn "s" .i64 (.int 0)
    (.seq (.while cond body) (.raise (.var "s"))))), ⟨false, some .i64, [], [], none⟩, {}⟩

private def sumBody : Expr := .seq (.assign ⟨"s", []⟩ (add (.var "s") (.var "i"))) (step "i" .add 1)

example : (counted 10 (lt (.var "i") (.var "n")) sumBody).divFree = true := rfl
example : ((counted 10 (lt (.var "i") (.var "n")) sumBody).runCopy 18).observe = .raised (.int 45) := rfl
example : ((counted 10 (lt (.var "i") (.var "n")) sumBody).runCopy 17).observe = .outOfFuel := rfl
example : ((counted 20 (lt (.var "i") (.var "n")) sumBody).runCopy 18).observe = .outOfFuel := rfl

/-- `n > i`, the mirror, and `i < n && s < 100`, the first conjunct of a chain, count too. -/
example : (counted 10 (.op (.compare .gt .i64) [.var "n", .var "i"]) sumBody).divFree = true := rfl
example : (counted 10 (.if (lt (.var "i") (.var "n")) .bool (lt (.var "s") (.int 100)) (.bool false))
    sumBody).divFree = true := rfl

/-- `while i < n { i = i + 0 }`, `while i < n { if s < 0 { i = i + 1 } }`, a `continue`
before the step, a step away from the bound, and a body that writes `n` don't count. -/
example : (counted 10 (lt (.var "i") (.var "n")) (step "i" .add 0)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n"))
    (.if (lt (.var "s") (.int 0)) .unit (step "i" .add 1) .unit)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n"))
    (.seq (.if (lt (.var "s") (.int 0)) .unit .continue .unit) (step "i" .add 1))).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n")) (step "i" .sub 1)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n")) (.seq (step "n" .add 1) (step "i" .add 1))).divFree = false :=
  rfl

end Stilt.Examples.Ends
