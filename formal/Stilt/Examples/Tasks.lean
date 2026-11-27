import Stilt.Tasks.Scopes
import Stilt.Tasks.Lazy
import Stilt.Modes.Demands
import Stilt.Semantics

/-!
# Tasks, scopes and lazy values

Runs of the forms of tasks in the sequential run (tasks.sequential-run): `spawn` runs the task's
function to its end before it returns, so what the task prints comes before what the code after
the `spawn` prints, and `await` gives the value the task ended with, as often as it is called; a
task of a scope that raises raises at `s.spawn`, and the code after it never runs
(tasks.scope-failure). Then E0434 (tasks.scope-that-escapes) on a task's function that captures
its scope, and on a scope given to a parameter of its type, and E0435
(polymorphism.lazy-waits-for-nothing) on a lazy value's function that runs a `when`, written
where it is given or bound by a `let` to the local given; and E0432 (shared.tasks-and-modes) on a
task's function that captures a view.
-/

namespace Stilt.Examples.Tasks

private def task : RecordDecl := ⟨taskName, [("value", .param "T")], ["T"]⟩
private def scope : RecordDecl := ⟨scopeName, [], ["T"]⟩
private def lazy : RecordDecl := ⟨lazyName, [("get", .fn [] (.param "T") Row.pure)], ["T"]⟩

private def decls (fns : List FnDecl := []) : Decls := ⟨[task, scope, lazy], [], fns, [], [], [], [], []⟩

/-- What a run ends with, a value or a raise, and the output it wrote. -/
private def shown : Outcome Copy.State Value → Option (Value × String)
  | .done v s | .raised v s => some (v, s.2.out)
  | _ => none

private def io : Row := ⟨true, none, [], [], none⟩
private def ioRaise : Row := ⟨true, some .i64, [], [], none⟩

private def print (s : String) : Expr := .op (.world (.write false true)) [.op (.str s) []]

/-- `spawn(|| { print("task"); 1 })`. -/
private def spawned (g : Name) : Expr :=
  .spawnOf taskName g io (.closure [] .i64 io (.seq (print "task") (.int 1))) .i64

/-- `let t = spawn(|| { print("task"); 1 }); print("after"); t.await() + t.await()`, run from
the start, ends with `2`, the task's output before the code's after the `spawn`. -/
example : shown (eval (decls) Copy.memory 64
    (.letIn "t" (.record taskName [.i64]) (spawned "g")
      (.seq (print "after")
        (.op (.arith .add .i64) [.awaitOf taskName "h" .i64 (.var "t"),
          .awaitOf taskName "k" .i64 (.var "t")]))) ([], World.start "")) =
      some (.int 2, "task\nafter\n") := rfl

/-- In a scope whose function raises at its first `s.spawn`, the code after it never runs:
`task.scope(|s| { try s.spawn(|| raise 7); print("after"); 0 })` raises `7` and prints
nothing. -/
example : shown (eval (decls) Copy.memory 64
    (.scopeOf scopeName .i64
      (.closure [⟨.let, "s", .record scopeName [.i64], none⟩] .i64 ioRaise
        (.seq (.try (.scopeSpawnOf scopeName "r" .i64 (.var "s") taskName "g" ioRaise
            (.closure [] .i64 ioRaise (.raise (.int 7))) .i64))
          (.seq (print "after") (.int 0)))) .i64) ([], World.start "")) = some (.int 7, "") :=
  rfl

/-- `|s| s.spawn(|| 1)`: the receiver of `spawn` is a use a scope may have. -/
private def receiver : Expr :=
  .closure [⟨.let, "s", .record scopeName [.i64], none⟩] .i64 ioRaise
    (.form .await (.letIn "h" (.record taskName [.i64])
      (.scopeSpawnOf scopeName "r" .i64 (.var "s") taskName "g" ioRaise
        (.closure [] .i64 ioRaise (.int 1)) .i64) (.field (.var "h") "value")))

/-- `|s| s.spawn(|| s.spawn(|| 1).await())`: the task's function captures the scope. -/
private def captured : Expr :=
  .closure [⟨.let, "s", .record scopeName [.i64], none⟩] .i64 ioRaise
    (.scopeSpawnOf scopeName "r" .i64 (.var "s") taskName "g" ioRaise
      (.closure [] .i64 ioRaise
        (.awaitOf taskName "h" .i64 (.scopeSpawnOf scopeName "q" .i64 (.var "s") taskName "k"
          ioRaise (.closure [] .i64 ioRaise (.int 1)) .i64))) .i64)

/-- `fn passed(s: Scope<i64>) -> i64` and `|s| passed(s)`: a scope given to a parameter of its
type. -/
private def passed : FnDecl :=
  ⟨"passed", [], [], [⟨.let, "s", .record scopeName [.i64], none⟩], .i64, ioRaise, .int 2, {}⟩

private def program (fns : List FnDecl) (f : Expr) : Program :=
  ⟨decls fns, .scopeOf scopeName .i64 f .i64, ioRaise, {}⟩

example : (program [] receiver).ScopesKept := by unfold Program.ScopesKept; decide

/-- E0434: a task's function that captures its scope. -/
example : ¬ (program [] captured).ScopesKept := by unfold Program.ScopesKept; decide

example : (program [passed] (.closure [⟨.let, "s", .record scopeName [.i64], none⟩] .i64 ioRaise
    (.call (.fnRef "passed" [] []) [.value (.var "s")] .i64))).ScopesKept := by
  unfold Program.ScopesKept; decide

/-- E0434: a scope given to a parameter of another type, which keeps it. -/
example : ¬ (program [⟨"kept", [], [], [⟨.let, "s", .unit, none⟩], .i64, ioRaise, .int 2, {}⟩]
    (.closure [⟨.let, "s", .record scopeName [.i64], none⟩] .i64 ioRaise
      (.call (.fnRef "kept" [] []) [.value (.var "s")] .i64))).ScopesKept := by
  unfold Program.ScopesKept; decide

/-- `when a { () }`. -/
private def hold : Expr := .held [("a", .i64)] [.var "a"] .unit

private def lazyProgram (main : Expr) : Program := ⟨decls, main, Row.pure, {}⟩

/-- E0435: `Lazy.new(|| { when a { () }; 1 })`. -/
example : ¬ (lazyProgram (.lazyNewOf lazyName .i64
    (.closure [] .i64 Row.pure (.seq hold (.int 1))))).LazyLocks := by
  unfold Program.LazyLocks; decide

/-- E0435: `let f = || { when a { () }; 1 }; Lazy.new(f)`. -/
example : ¬ (lazyProgram (.letIn "f" (.fn [] .i64 Row.pure)
    (.closure [] .i64 Row.pure (.seq hold (.int 1))) (.lazyNewOf lazyName .i64 (.var "f")))).LazyLocks := by
  unfold Program.LazyLocks; decide

/-- `let f = || 1; Lazy.new(f)` is accepted, and so is a function value given: no check sees what
it calls. -/
example : (lazyProgram (.letIn "f" (.fn [] .i64 Row.pure) (.closure [] .i64 Row.pure (.int 1))
    (.lazyNewOf lazyName .i64 (.var "f")))).LazyLocks := by
  unfold Program.LazyLocks; decide

/-- `spawn(|| x)`, a task whose function captures `x`. -/
private def taskOn (x : Name) (τ : Ty) : Expr :=
  .spawnOf taskName "g" io (.closure [] τ io (.var x)) τ

/-- E0432: a task's function that captures a view is `fixed`; one that captures a list is
`portable`. -/
example : ((taskOn "w" (.view (.list .i64))).demandsMet (decls) [⟨.let, "w", .view (.list .i64), none⟩],
    (taskOn "xs" (.list .i64)).demandsMet (decls) [⟨.let, "xs", .list .i64, none⟩]) =
    (false, true) := by decide

end Stilt.Examples.Tasks
