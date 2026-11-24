import Stilt.Writes.Agreement

/-!
# The required tests of projections.writable-views and projections.what-view-writes

The required tests of projections.writable-views and projections.what-view-writes that the calculus of writable views states: runs
of `view.into` and of writes through `v[i]`, in both models, with the `bounds`
panics at each offset that projections.writable-views rejects; E0429 and what it accepts
(projections.what-view-writes); E0428 and the bindings that read (projections.writable-bindings and projections.places-through-views). A program here
is a block with no parameters. Tests of projections, calls, `view.part`,
`view.split`, loops and `show` are outside the calculus.
-/

namespace Stilt.Writes

section RequiredTests

private def list (ks : List Int) : WExpr := .list .i64 (ks.map .int)

private def xs : WExpr := .var "xs"

private def v : WExpr := .var "v"

private def viewTy : Stilt.Views.VTy := .view (.list .i64)

/-- `var xs = [10, 20, 30, 40]`, followed by `rest`. -/
private def withList (rest : WExpr) : WExpr := .varIn "xs" (.base (.list .i64)) (list [10, 20, 30, 40]) rest

/-- `var v = view.into(inout xs, a, b)`, followed by `rest`. -/
private def withInto (a b : Int) (rest : WExpr) : WExpr :=
  .varIn "v" viewTy (.into xs (.int a) (.int b)) rest

/-- `v[k] = e`. -/
private def put (k e : Int) : WExpr := .assign (.index v (.int k)) (.int e)

/-- What both models show of a block. -/
private def shows (e : WExpr) (o : Observation) : Prop :=
  (⟨.base .i64, e⟩ : WProgram).observe .window 40 = o ∧
    (⟨.base .i64, e⟩ : WProgram).observe .copy 40 = o

/-- The law with the reads and writes of views. -/
private def lawful (e : WExpr) : Bool := e.exclusive true [] [] []

/-! ### Runs (projections.writable-views and projections.places-through-views) -/

/-- Writes through `v[i]` of `view.into(inout xs, 1, 3)` reach `xs` once the
binding's scope ends, and `v[0]` reads what was written. -/
example : shows (withList (.seq (withInto 1 3 (.seq (put 0 5) (put 1 6))) (.index xs (.int 2))))
    (.returned (.int 6)) := ⟨rfl, rfl⟩
example : shows (withList (withInto 1 3 (.seq (put 0 5) (.index v (.int 0)))))
    (.returned (.int 5)) := ⟨rfl, rfl⟩
example : shows (withList (withInto 1 3 (.len v))) (.returned (.int 2)) := ⟨rfl, rfl⟩

/-- `bounds` at each offset that projections.writable-views rejects, and at a write outside the
part. -/
example : shows (withList (withInto (-1) 2 (.len v))) (.panicked .bounds) := ⟨rfl, rfl⟩
example : shows (withList (withInto 3 2 (.len v))) (.panicked .bounds) := ⟨rfl, rfl⟩
example : shows (withList (withInto 0 5 (.len v))) (.panicked .bounds) := ⟨rfl, rfl⟩
example : shows (withList (withInto 1 3 (.seq (put 2 1) (.len v)))) (.panicked .bounds) :=
  ⟨rfl, rfl⟩

/-! ### Writing (projections.what-view-writes) and E0429 -/

/-- E0429 for a read of the source, a modification of it, a view of it, and
a view that writes it, while a writable binding writes it. -/
example : lawful (withList (withInto 0 2 (.index xs (.int 0)))) = false := by decide
example : lawful (withList (withInto 0 2 (.assign (.index xs (.int 0)) (.int 1)))) = false := by
  decide
example : lawful (withList (withInto 0 2 (.len (.viewOf xs (.int 0) (.int 1))))) = false := by
  decide
example : lawful (withList (withInto 0 2 (.len (.into xs (.int 0) (.int 1))))) = false := by
  decide

/-- Accepted: reaching the source after the binding's scope ends, and before
the view is made. -/
example : lawful (withList (.seq (withInto 0 2 (put 0 1)) (.index xs (.int 0)))) = true := by
  decide
example : lawful (withList (.seq (.index xs (.int 0)) (withInto 0 2 (put 0 1)))) = true := by
  decide

/-! ### Bindings (projections.writable-bindings and projections.places-through-views) and E0428 -/

/-- E0428 for `var v = View.of(xs, 0, 1)` and `var w = v` of a writable `v`. -/
example : (withList (.varIn "v" viewTy (.viewOf xs (.int 0) (.int 1)) (.len v))).bound = false := by
  decide
example : (withList (withInto 0 2 (.varIn "w" viewTy v (.len (.var "w"))))).bound = false := by
  decide

/-- Accepted: `let w = view.into(inout xs, 0, 1)`, which reads, so that `xs` is
read while it lives. -/
example : lawful (withList (.letIn "w" viewTy (.into xs (.int 0) (.int 1)) (.index xs (.int 0)))) =
    true := by decide

/-- `let w = v.view(0, 1)` has `v` as its source: E0423 on `v[0] = 1` while
`w` lives, and accepted without it. -/
example : lawful (withList (withInto 0 2 (.letIn "w" viewTy (.sub v (.int 0) (.int 1))
    (.seq (put 0 1) (.len (.var "w")))))) = false := by decide
example : lawful (withList (withInto 0 2 (.letIn "w" viewTy (.sub v (.int 0) (.int 1))
    (.len (.var "w"))))) = true := by decide

end RequiredTests

end Stilt.Writes
