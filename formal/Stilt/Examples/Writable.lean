import Stilt.Exclusivity
import Stilt.Semantics
import Stilt.ViewReads
import Stilt.Windows.Eval
import Stilt.Writable

/-!
# Writable views

Runs of writable bindings in the models of copies, of in-place mutation and of windows, as the
forms of `Stilt.Writable` write them, and the checks of writable bindings on them. A writable
binding's scope is a call of a closure literal that takes its source `inout`
(projections.writable-bindings): copy-in, copy-out writes the part back when the scope ends, and
in place and with windows the writes reach the source's storage at once
(projections.what-view-writes). A place through the binding is a place of the source's parameter
at the index `Expr.throughOf` gives, which panics with `bounds` past the part's end, though not
past the source's (projections.places-through-views). Each program raises the value it shows, as
in `Stilt.Examples`.
-/

namespace Stilt.Examples.Writable

private def ints : Ty := .list .i64

/-- A program from `main`, whose row is `raise<i64>`. -/
private def program (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], [], []⟩, main, ⟨false, some .i64, [], [], none⟩, {}⟩

/-- The three models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o ∧ (p.runWindows 64).observe = o

private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]
private def at0 (xs : Name) (i : Int) : Expr := .index (.var xs) (.int i)

/-- `v[i]` as a place, through the binding of `src` from `s` to `e`. -/
private def through (i : Int) : List Projection := [.index (.throughOf "j" "s" "e" (.int i))]

/-- `var v = view.into(inout xs, a, b)` and `body`, the rest of its block, which writes `v`
through `src`: the offsets bound, the source checked as `View.of` checks it, then the call. -/
private def into (a b : Int) (body : Expr) (captures : Bool := false) : Expr :=
  .letIn "s" .i64 (.int a) (.letIn "e" .i64 (.int b)
    (.seq (.view [.var "xs", .var "s", .var "e"])
      (.form .writes (.call
        (.closure [⟨.inout, "src", ints, none⟩] .unit Row.pure
          (if captures then .seq (.var "xs") body else body))
        [.inout ⟨"xs", []⟩] .unit))))

/-- `var xs = [1, 2, 3, 4]`, `scope`, then `xs`'s sum raised. -/
private def withList (scope : Expr) : Expr :=
  .varIn "xs" ints (.list .i64 [.int 1, .int 2, .int 3, .int 4])
    (.seq scope (.raise (add (add (at0 "xs" 0) (at0 "xs" 1)) (add (at0 "xs" 2) (at0 "xs" 3)))))

/-- `{ var v = view.into(inout xs, 1, 3); v[0] = 10; v[1] += 5 }`. -/
private def written : Expr :=
  into 1 3 (.seq (.assign ⟨"src", through 0⟩ (.int 10))
    (.assign ⟨"src", through 1⟩ (add (.index (.view [.var "src", .var "s", .var "e"]) (.int 1)) (.int 5))))

/-- `xs` is `[1, 10, 8, 4]` in every model: written back in copies, written at once in place and
with windows. -/
example : agree (program (withList written)) (.raised (.int 23)) := ⟨rfl, rfl, rfl⟩

/-- projections/view_index_bounds: `{ var v = view.into(inout xs, 1, 3); v[2] = 9 }` panics with
`bounds`: the index is past the part's end, though `xs[3]` is a place. -/
example : agree (program (withList (into 1 3 (.assign ⟨"src", through 2⟩ (.int 9)))))
    (.panicked .bounds) := ⟨rfl, rfl, rfl⟩

/-- `view.into(inout xs, 3, 5)` panics with `bounds`, as `View.of` does. -/
example : agree (program (withList (into 3 5 .unit))) (.panicked .bounds) := ⟨rfl, rfl, rfl⟩

/-! ## The checks -/

/-- The writable binding keeps the rules of writable bindings, the law of exclusivity and
views.change-while-viewed. -/
example : (withList written).writesChecked = true ∧ (withList written).exclusive [] = true ∧
    (withList written).viewsRead (program .unit).decls [] [] = true := by
  decide

/-- A scope that reaches `xs` while the binding writes it is E0429
(projections.reaching-written-source). -/
example : (withList (into 1 3 .unit (captures := true))).writesChecked = false := by decide

/-- A `var` of a view type that no writable binding's form gives, `var v = View.of(xs, 0, 1)`,
is E0428 (projections.writable-bindings). -/
example : (withList (.varIn "v" (.view ints) (.view [.var "xs", .int 0, .int 1]) .unit)).writesChecked
    = false := by decide

end Stilt.Examples.Writable
