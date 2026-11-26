import Stilt.Exclusivity
import Stilt.Semantics
import Stilt.WellTyped
import Stilt.Windows.Eval

/-!
# Views

Runs of the required tests of views.making-view and views.functions-of-views, in the models of
copies, of in-place mutation and of windows, and the typing of a view. A view is the part it
reads, as the reference interpreter holds it (views.what-view-is): `View.of(xs, a, b)` is the
part that `xs.slice(a, b)` gives, which panics as `slice` does (views.making-view), and the
other functions of a view read the part through `copy` (views.functions-of-views). Each program
raises the value it shows, as in `Stilt.Examples`.
-/

namespace Stilt.Examples.Views

/-- A program from the type of the value it shows and `main`, whose row is
`raise<shown>`. -/
private def program (shown : Ty) (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], []⟩, main, ⟨false, some shown, [], [], none⟩, {}⟩

/-- The three models give the same observation, a raised window observed as its part. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o ∧ (p.runWindows 64).observe = o

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-- `View.of(source, a, b)` on a list. -/
private def viewOf (source : Expr) (a b : Int) : Expr :=
  .view [source, .int a, .int b]

/-- `v.copy()`. -/
private def copy (v : Expr) : Expr := .op .copy [v]

private def listView : Ty := .view (.list .i64)

/-- views/view_index_bounds: `let tail = View.of([1, 2, 3], 1, 3)`, then `tail[1]` is
`3`. -/
example : agree (program .i64
    (.letIn "tail" listView (viewOf (ints [1, 2, 3]) 1 3)
      (.raise (.index (copy (.var "tail")) (.int 1)))))
    (.raised (.int 3)) := ⟨rfl, rfl, rfl⟩

/-- `tail[2]` is past the part's end, and panics with `bounds`
(views.functions-of-views). -/
example : agree (program .i64
    (.letIn "tail" listView (viewOf (ints [1, 2, 3]) 1 3)
      (.raise (.index (copy (.var "tail")) (.int 2)))))
    (.panicked .bounds) := ⟨rfl, rfl, rfl⟩

/-- views/view_bounds: `View.of([1, 2], 2, 1)` panics with `bounds`, since its start is
past its end (views.making-view). -/
example : agree (program listView (.raise (viewOf (ints [1, 2]) 2 1)))
    (.panicked .bounds) := ⟨rfl, rfl, rfl⟩

/-- `v.view(1, 2)` of `View.of("abc", 0, 3)` is the part `"b"`, its offsets counted from
the view's start (views.making-view). -/
example : agree (program .str
    (.letIn "v" (.view .str) (.view [.op (.str "abc") [], .int 0, .int 3])
      (.raise (copy (.view [.var "v", .int 1, .int 2])))))
    (.raised (.str "b")) := ⟨rfl, rfl, rfl⟩

/-- A view of a list has the view type, and its `copy` the list's type
(views.making-view and views.functions-of-views). -/
example : HasType ⟨[], [], [], [], [], [], []⟩ RowScope.closed [] ⟨Row.pure, false, false, .never, false, false⟩
    (copy (.view [ints [1]])) (.list .i64) := by
  have hwf : Ty.i64.WellFormed RowScope.closed :=
    ⟨fun _ h => by simp [Ty.rows] at h, fun _ h => by simp [Ty.params] at h,
      fun _ h => by simp [Ty.rows] at h, fun _ h => by simp [Ty.views] at h⟩
  refine .op .copy (.cons (.view (.viewAll rfl) (.cons ?_ (.refl _) .nil)) (.refl _) .nil)
  exact .list hwf (.cons (.int (by decide)) (.refl _) .nil)

/-- Only `str` and lists are viewable: `View.all(1)` has no type (views.viewable-types,
E0420). -/
example (τ : Ty) : ¬ Op.Sig .view [.i64] τ := by
  intro h
  cases h with
  | viewAll h => simp [Ty.viewable] at h

end Stilt.Examples.Views
