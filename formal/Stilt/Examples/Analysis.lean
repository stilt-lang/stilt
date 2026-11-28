import Stilt.Analysis.Agree.Theorem

/-!
# What the analysis proves

Bodies whose marks the analysis proves whole, or doesn't (`Expr.verified`): a literal index of a
list literal, a division by a literal, one guarded by `d != 0`, a store at a range loop's
variable over `0..xs.len()`, a `while` whose counter starts at zero and only grows, and a sum
of small known values on `i8`; not an unguarded division, a store over `0..=xs.len()`, nor a
sum that may overflow. A release build of each drops the checks the analysis proves and runs
as the reference interpreter does (`Program.runRelease_eq`).
-/

namespace Stilt.Examples.Analysis

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def proved (k : PanicKind) (e : Expr) : Expr := .form (.proved [k]) e
private def div (a b : Expr) : Expr := .op (.arith .div .i64) [a, b]
private def len (xs : Name) : Expr := .op (.list .len) [.var xs]

/-- `let xs = [1, 2, 3]; xs[2]`. -/
example : (Expr.letIn "xs" (.list (.int .i64)) (.list (.int .i64) [.int 1, .int 2, .int 3])
    (proved .bounds (.index (.var "xs") (.int 2)))).verified = true := by decide

example : (Expr.letIn "xs" (.list (.int .i64)) (.list (.int .i64) [.int 1, .int 2, .int 3])
    (proved .bounds (.index (.var "xs") (.int 3)))).verified = false := by decide

/-- `n / 2`, `n / d` and `if d != 0 { n / d } else { 0 }`. -/
example : (proved .divideByZero (div (.var "n") (.int 2))).verified = true := by decide

example : (proved .divideByZero (div (.var "n") (.var "d"))).verified = false := by decide

example : (Expr.if (.op (.compare .ne .i64) [.var "d", .int 0]) (.int .i64)
    (proved .divideByZero (div (.var "n") (.var "d"))) (.int 0)).verified = true := by decide

/-- `for i in 0..xs.len() { xs[i] = 0 }`, and not over `0..=xs.len()`. -/
private def storeAll (inclusive : Bool) : Expr :=
  .for "i" (.int .i64) (.op (.list (.range inclusive)) [.int 0, len "xs"])
    (proved .bounds (.assign ⟨"xs", [.index (.var "i")]⟩ (.int 0)))

example : (storeAll false).verified = true := by decide

example : (storeAll true).verified = false := by decide

/-- `var i = 0; while i < xs.len() { xs[i] = 0; i = i + 1 }`: the loop's head keeps `i >= 0`. -/
example : (Expr.varIn "i" (.int .i64) (.int 0)
    (.while (.op (.compare .lt .i64) [.var "i", len "xs"])
      (.seq (proved .bounds (.assign ⟨"xs", [.index (.var "i")]⟩ (.int 0)))
        (.assign ⟨"i", []⟩ (.op (.arith .add .i64) [.var "i", .int 1]))))).verified = true := by
  decide

/-- `let a = 3; a + 4` on `i8`, and not `a + b` of an unknown `b`. -/
example : (Expr.letIn "a" (.int .i8) (.int 3)
    (proved .overflow (.op (.arith .add .i8) [.var "a", .int 4]))).verified = true := by decide

example : (Expr.letIn "a" (.int .i8) (.int 3)
    (proved .overflow (.op (.arith .add .i8) [.var "a", .var "b"]))).verified = false := by decide

end Stilt.Examples.Analysis
