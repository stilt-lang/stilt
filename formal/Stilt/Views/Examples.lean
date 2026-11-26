import Stilt.Views.Agreement

/-!
# The required tests of the views

The required tests of the views that the calculus of views can state: runs of
`View.of`, `view`, `len`, indexing, `copy` and `for` over a view on lists, in
both models, with the `bounds` panics at each offset that views.making-view rejects; the
durations of views.reads-that-last, which E0423 checks; and the escapes of views.escaping, which
E0422 checks. A program here is a body with no parameters, unless it says
otherwise. Tests of strings, calls, closures and iterators are outside the
calculus.
-/

namespace Stilt.Views

section RequiredTests

private def list (ks : List Int) : VExpr := .list .i64 (ks.map .int)

/-- A body whose parameter `xs` holds `[10, 20, 30, 40]`. -/
private def body (result : VTy) (e : VExpr) : VProgram :=
  ⟨⟨[], [], [], [], [], [], []⟩, [("xs", .list .i64, .list ([10, 20, 30, 40].map .int))], result, e⟩

private def xs : VExpr := .var "xs"

private def v : VExpr := .var "v"

/-- `var xs = [10, 20, 30, 40]`, followed by `rest`. -/
private def withList (rest : VExpr) : VExpr := .varIn "xs" (.list .i64) (list [10, 20, 30, 40]) rest

/-- `let v = View.of(xs, a, b)`, followed by `rest`. -/
private def withView (a b : Int) (rest : VExpr) : VExpr :=
  .letIn "v" (.view (.list .i64)) (.viewOf xs (.int a) (.int b)) rest

/-- What both models show of a body. -/
private def shows (p : VProgram) (o : Observation) : Prop :=
  p.observe .window 30 = o ∧ p.observe .copy 30 = o

/-! ### Runs -/

/-- `View.of(xs, 1, 3)` shows `[20, 30]`, its `len()` is 2 and `v[1]` is 30. -/
example : shows (body (.view (.list .i64)) (.viewOf xs (.int 1) (.int 3)))
    (.returned (.list [.int 20, .int 30])) := ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 1 3 (.len v))) (.returned (.int 2)) :=
  ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 1 3 (.index v (.int 1))))
    (.returned (.int 30)) := ⟨rfl, rfl⟩

/-- `v.view(1, 2)` of `View.of(xs, 1, 4)` is `[30]`, and `copy` gives the
part as a list. -/
example : shows (body (.base (.list .i64)) (withView 1 4 (.copy (.sub v (.int 1) (.int 2)))))
    (.returned (.list [.int 30])) := ⟨rfl, rfl⟩

/-- A view of a temporary, `View.of([1, 2, 3], 2, 3)`. -/
example : shows (body (.base .i64) (.index (.viewOf (list [1, 2, 3]) (.int 2) (.int 3)) (.int 0)))
    (.returned (.int 3)) := ⟨rfl, rfl⟩

/-- `bounds` at each offset that views.making-view rejects: a negative start, a start
after the end, an end past the length; and at an index outside the part. -/
example : shows (body (.base .i64) (withView (-1) 2 (.len v))) (.panicked .bounds) :=
  ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 3 2 (.len v))) (.panicked .bounds) :=
  ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 0 5 (.len v))) (.panicked .bounds) :=
  ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 1 3 (.index v (.int 2))))
    (.panicked .bounds) := ⟨rfl, rfl⟩
example : shows (body (.base .i64) (withView 1 3 (.len (.sub v (.int 1) (.int 3)))))
    (.panicked .bounds) := ⟨rfl, rfl⟩

/-- A view in a `for`: `var last = 0; for x in View.of(xs, 1, 3) { last = x }`
leaves 30. -/
example : shows (body (.base .i64) (.varIn "last" .i64 (.int 0)
    (.seq (.for "x" .i64 (.viewOf xs (.int 1) (.int 3)) (.assign (.var "last") (.var "x")))
      (.var "last")))) (.returned (.int 30)) := ⟨rfl, rfl⟩

/-! ### Durations (views.reads-that-last) and E0423 (views.change-while-viewed) -/

/-- The law with the reads of views, from a body with no parameters. -/
private def lawful (e : VExpr) : Bool := e.exclusive true [] []

/-- E0423 for a modification of the source, of a part of it, and of a
containing place, while a view binding lives. -/
example : lawful (withList (withView 0 2 (.seq (.assign xs (list [])) (.len v)))) = false := by
  decide
example :
    lawful (withList (withView 0 2 (.seq (.assign (.index xs (.int 0)) (.int 1)) (.len v)))) =
      false := by decide
example :
    lawful (.varIn "r" (.record "R" []) (.record "R" [("a", list [1]), ("b", list [2])])
      (.letIn "v" (.view (.list .i64)) (.viewOf (.field (.var "r") "a") (.int 0) (.int 1))
        (.seq (.assign (.var "r") (.record "R" [("a", list []), ("b", list [])])) (.len v)))) =
      false := by decide

/-- E0423 inside a `for` over a view, whose view reads its sources for the
body (views.for-over-view). -/
example :
    lawful (withList (.for "x" .i64 (.viewOf xs (.int 0) (.int 2))
      (.assign (.index xs (.int 0)) (.var "x")))) = false := by decide

/-- E0423 for a change made while the index of `v[i]` is evaluated, in the
view that no binding holds. -/
example :
    lawful (withList (.index (.viewOf xs (.int 0) (.int 2))
      (.seq (.assign xs (list [])) (.int 0)))) = false := by decide

/-- Accepted: a modification after the binding's scope ends, before the view
is made, of a place that doesn't overlap the source, and of the source after
a view that no binding holds has been read in its statement. -/
example :
    lawful (withList (.seq (withView 0 2 (.len v)) (.assign (.index xs (.int 0)) (.int 1)))) =
      true := by decide
example :
    lawful (withList (.seq (.assign (.index xs (.int 0)) (.int 1)) (withView 0 2 (.len v)))) =
      true := by decide
example :
    lawful (.varIn "r" (.record "R" []) (.record "R" [("a", list [1]), ("b", list [2])])
      (.letIn "v" (.view (.list .i64)) (.viewOf (.field (.var "r") "a") (.int 0) (.int 1))
        (.seq (.assign (.index (.field (.var "r") "b") (.int 0)) (.int 3)) (.len v)))) =
      true := by decide
example :
    lawful (withList (.letIn "n" (.base .i64) (.len (.viewOf xs (.int 0) (.int 2)))
      (.seq (.assign (.index xs (.int 0)) (.int 1)) (.var "n")))) = true := by decide

/-- A new `xs` hides the viewed one, so changing it is accepted. -/
example :
    lawful (withList (withView 0 2 (.varIn "xs" (.list .i64) (list [1])
      (.seq (.assign (.index xs (.int 0)) (.int 2)) (.len v))))) = true := by decide

/-- E0404 still rejects a change to a list inside a `for` over it, and the
law with the reads of views alone accepts it. -/
example :
    lawful (withList (.for "x" .i64 xs (.assign (.index xs (.int 0)) (.var "x")))) = false := by
  decide
example :
    (withList (.for "x" .i64 xs (.assign (.index xs (.int 0)) (.var "x")))).exclusive false [] [] =
      true := by decide

/-! ### Escapes (views.escaping) and E0422 -/

/-- E0422 for a view of a local returned, directly or through a binding. -/
example : (withList (.viewOf xs (.int 0) (.int 1))).contained [] = false := by decide
example : (withList (withView 0 1 v)).contained [] = false := by decide

/-- Accepted: a view of a `let` parameter returned, and a view of a local
that the body reads before its scope ends. -/
example : (VExpr.viewOf xs (.int 0) (.int 1)).contained [("xs", [])] = true := by decide
example : (withList (withView 0 1 (.copy v))).contained [] = true := by decide

end RequiredTests

end Stilt.Views
