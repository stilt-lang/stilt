import Stilt.Locks.Theorem

/-!
# `locks` and E0430

The fact of shared.locks on a few declarations: `inner` runs a `when`, `outer` calls
`inner`, `stored` uses `inner` as a value, and `through` calls a function value it is given.
Each but `through` has the fact: a call through a function value adds nothing
(facts.calls-through-function-values). A `when` whose block calls `outer`, or holds a closure
literal whose body runs a `when`, is E0430; one whose block calls `through` is accepted.
-/

namespace Stilt.Examples.Locks

private def shared : Ty := .shared .i64

/-- `when a { () }`, `a` a handle. -/
private def hold : Expr := .held [("a", .i64)] [.var "a"] .unit

private def callOf (f : Expr) : Expr := .call f [] .unit

private def fn (name : Name) (params : List Param) (body : Expr) : FnDecl :=
  ⟨name, [], [], params, .unit, Row.pure, body, {}⟩

private def decls : Decls :=
  ⟨[], [], [
    fn "inner" [⟨.let, "a", shared, none⟩] hold,
    fn "outer" [] (callOf (.fnRef "inner" [] [])),
    fn "stored" [] (.letIn "g" (.fn [] .unit Row.pure) (.fnRef "inner" [] []) .unit),
    fn "through" [⟨.let, "g", .fn [] .unit Row.pure, none⟩] (callOf (.var "g"))],
    [], [], [], [], []⟩

/-- `inner`, `outer` and `stored` have the fact, `through` doesn't. -/
example : decls.locks = ["inner", "outer", "stored"] := by decide

/-- A `when` whose block holds the block `b`, in `main`. -/
private def program (b : Expr) : Program := ⟨decls, .held [("a", .i64)] [.var "a"] b, Row.pure, {}, {}⟩

/-- `when a { outer() }` is E0430. -/
example : ¬ (program (callOf (.fnRef "outer" [] []))).Locks := by
  unfold Program.Locks; decide

/-- `when a { let f = || { when a { () } }; () }` is E0430: a closure literal's body is part of
the code that writes it. -/
example : ¬ (program (.letIn "f" (.fn [] .unit Row.pure) (.closure [] .unit Row.pure hold)
    .unit)).Locks := by
  unfold Program.Locks; decide

/-- `when a { through(g) }` is accepted, whatever `g` does. -/
example : (program (.call (.fnRef "through" [] []) [.value (.var "g")] .unit)).Locks := by
  unfold Program.Locks; decide

end Stilt.Examples.Locks
