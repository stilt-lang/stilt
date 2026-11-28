import Stilt.OneShot.Theorem

/-!
# One-shot handlers

The check of handlers.resume-at-most-once on the bodies of handlers that take
control: `resume(resume(1))`, a `resume` in a loop, in a closure literal, and
after a branch that resumed are each E0514, while one in each arm of an `if`
passes; a call as code of a body that takes control is stuck
(handlers.resume-outside-operation). And runs, in both models of memory, of a
call whose `inout` argument is live across a performance: resumed, the call
goes on and writes its argument back when it ends (handlers.resuming); ended
by a handler that never resumes, it writes back what it changed before the
performance, as on a raise (handlers.call-that-handler-ends). Each program
raises the list of the values it shows, as in `Stilt.Examples`.
-/

namespace Stilt.Examples.OneShot

private def ask : Operation := ⟨"Ask", "ask"⟩
private def fail : Operation := ⟨"Fail", "fail"⟩

private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]
private def resume (e : Expr) : Expr := .perform Operation.resume e

private def row (E : Name) : Row := ⟨false, none, [], [E], none⟩
private def controlRow : Row := ⟨false, none, [], [], some (.i64, .i64)⟩

/-- `handler E -> i64 { fn op(x: A) -> i64 { body } }`, as the record of its one closure. -/
private def handler (R op : Name) (A : Ty) (body : Expr) : Expr :=
  .record R [] [(op, .closure [⟨.let, "x", A, none⟩] .i64 controlRow body)]

/-- `handler Ask -> i64 { fn ask() -> i64 { let r = resume(10); r + 100 } }`. -/
private def around : Expr :=
  handler "AroundAsk" "ask" .unit (.letIn "r" .i64 (resume (.int 10)) (add (.var "r") (.int 100)))

/-- `handler Fail -> i64 { fn fail(n: i64) -> i64 { -1 } }`, which never resumes. -/
private def toDefault : Expr := handler "ToDefault" "fail" .i64 (.int (-1))

/-- `fn bump(inout x: i64) / Ask { x = x + Ask.ask() }` and
`fn spend(inout x: i64) / Fail { x = x + 5; Fail.fail(x); x = 0 }`. -/
private def fns : List FnDecl := [
  ⟨"bump", [], [], [⟨.inout, "x", .i64, none⟩], .unit, row "Ask",
    .assign ⟨"x", []⟩ (add (.var "x") (.perform ask .unit)), {}⟩,
  ⟨"spend", [], [], [⟨.inout, "x", .i64, none⟩], .unit, row "Fail",
    .seq (.assign ⟨"x", []⟩ (add (.var "x") (.int 5)))
      (.seq (.perform fail (.var "x")) (.assign ⟨"x", []⟩ (.int 0))), {}⟩]

private def decls : Decls :=
  ⟨[⟨"AroundAsk", [("ask", .fn [(.let, .unit)] .i64 controlRow)], []⟩,
      ⟨"ToDefault", [("fail", .fn [(.let, .i64)] .i64 controlRow)], []⟩],
    [], fns, [], [], [], [⟨"Ask", [("ask", .unit, .i64)]⟩, ⟨"Fail", [("fail", .i64, .i64)]⟩], []⟩

/-- `f(inout n)`. -/
private def callInout (f : Name) : Expr := .call (.fnRef f [] []) [.inout ⟨"n", []⟩] .unit

/-- A program whose `main` binds `var n = 1` and raises the list of `es`' values. -/
private def program (es : List Expr) : Program :=
  ⟨decls, .varIn "n" .i64 (.int 1) (.raise (.list .i64 es)), ⟨false, some (.list .i64), [], [], none⟩, {}, {}⟩

private def areInts : List Value → List Int → Bool
  | [], [] => true
  | .int k :: vs, k' :: ks => k == k' && areInts vs ks
  | _, _ => false

/-- Both models show the raise of the list of `ks`. -/
private def raises (p : Program) (ks : List Int) : Bool :=
  let shows : Observation → Bool
    | .raised (.list vs) => areInts vs ks
    | _ => false
  shows (p.runCopy 64).observe && shows (p.runInPlace 64).observe

/-- Both models are stuck. -/
private def stuck (p : Program) : Bool :=
  let isStuck : Observation → Bool
    | .stuck => true
    | _ => false
  isStuck (p.runCopy 64).observe && isStuck (p.runInPlace 64).observe

/-! ## The check -/

/-- A handler's body passes when it resumes at most once on each path. -/
private def passes (body : Expr) : Bool := (handler "AroundAsk" "ask" .unit body).oneShot

private def cond : Expr := .bool true

example : passes (.letIn "r" .i64 (resume (.int 10)) (add (.var "r") (.int 100))) := by decide
example : passes (.if cond .i64 (resume (.int 1)) (resume (.int 2))) := by decide
example : passes (.int (-1)) := by decide

/-- E0514: twice in sequence, in a loop, in a closure literal, and after a
branch that resumed. -/
example : ¬ passes (resume (resume (.int 1))) := by decide
example : ¬ passes (.seq (.loop (.seq (resume (.int 1)) .break)) (.int 0)) := by decide
example : ¬ passes (.seq (.closure [] .i64 Row.pure (resume (.int 1))) (.int 0)) := by decide
example : ¬ passes (.seq (.if cond .i64 (resume (.int 1)) (.int 0)) (resume (.int 2))) := by decide

/-- The programs below pass the check. -/
example : (program [.withH "Ask" true around (.seq (callInout "bump") (.var "n")), .var "n"]).OneShot :=
  ⟨by decide, by decide, by decide⟩

/-- A call as code of a body that takes control is stuck: only a `with` calls it. -/
example : stuck (program [.call (.field around "ask") [.value .unit] .i64]) := by decide +kernel

/-! ## `inout` across a performance -/

/-- The body resumes with 10: `bump` goes on, `n` becomes 11 when the call ends,
the block ends with 11, and the body gives 111. -/
example : raises (program [.withH "Ask" true around (.seq (callInout "bump") (.var "n")), .var "n"])
    [111, 11] := by decide +kernel

/-- The body never resumes: the `with` ends with -1, `spend` ends as on a raise,
writing back the 6 it stored before the performance, and `x = 0` never runs. -/
example : raises (program [.withH "Fail" true toDefault (.seq (callInout "spend") (.int 7)), .var "n"])
    [-1, 6] := by decide +kernel

end Stilt.Examples.OneShot
