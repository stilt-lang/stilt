import Stilt.Views.Agreement

/-!
# Views that outlive their reads

Programs of the calculus of views that show what `ViewAgreement` rests on, beside
`Stilt.Counterexamples.Windows`, which shows on the core calculus that windows need
views.change-while-viewed (E0423) and views.escaping (E0422):

* `viewShrunk` replaces a source with a shorter list while a view of it lives: the
  window reads past the end of the storage the source now has, which a
  compiler can't detect, so E0423 is a soundness rule and not a cost rule
  (views.change-while-viewed);
* `viewKept` returns a view of a `let` parameter, which views.escaping allows, and both
  models show its part.

`viewRelisted` changes a list inside a `for` over it, which E0404 rejects; both
models agree on it, since the loop reads the list itself, so E0404 is a cost
rule (modes.change-while-iterating).
-/

namespace Stilt.Counterexamples

open Stilt.Views

/-- No declarations. -/
private def noDecls : Decls := ⟨[], [], [], [], [], [], []⟩

/-- `xs`, a list of `i64`, as a variable. -/
private def xs : VExpr := .var "xs"

/-- `var xs = [1, 2, 3]`, followed by `rest`. -/
private def withList (rest : VExpr) : VExpr :=
  .varIn "xs" (.list .i64) (.list .i64 [.int 1, .int 2, .int 3]) rest

/-- `let v = View.of(xs, 0, 3)`, followed by `rest`. -/
private def withView (rest : VExpr) : VExpr :=
  .letIn "v" (.view (.list .i64)) (.viewOf xs (.int 0) (.int 3)) rest

theorem viewList_typed {Γ : Views.Ctx} :
    Views.HasType noDecls Γ (.list .i64 [.int 1, .int 2, .int 3]) (.base (.list .i64)) :=
  .list fun e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact .int

/-! ## A source that shrinks under a view -/

/-- `var xs = [1, 2, 3]; let v = View.of(xs, 0, 3); xs = []; v[2]`. -/
def viewShrunk : VProgram :=
  ⟨noDecls, [], .base .i64, withList (withView
    (.seq (.assign xs (.list .i64 [])) (.index (.var "v") (.int 2))))⟩

theorem viewShrunk_wellTyped : viewShrunk.WellTyped :=
  ⟨fun _ h => (nomatch h), .varIn viewList_typed (.letIn (.viewOf rfl (.var rfl) .int .int)
    (.seq (.assign (.var rfl) (.list fun _ h => (nomatch h))) (.viewIndex (.var rfl) .int)))⟩

theorem viewShrunk_contained : viewShrunk.Contained := by unfold VProgram.Contained; decide

theorem viewShrunk_not_exclusive : ¬viewShrunk.ViewsExclusive := by
  unfold VProgram.ViewsExclusive
  decide

/-- The window reads past the end of the storage its source now has, which
is `stuck`: E0423 keeps a view from reading freed or moved storage. The copy
returns the element it copied. -/
theorem viewShrunk_runs :
    viewShrunk.observe .window 20 = .stuck ∧ viewShrunk.observe .copy 20 = .returned (.int 3) :=
  ⟨rfl, rfl⟩

/-! ## A view of a parameter returned -/

/-- `fn f(xs: List<i64>) -> View<List<i64>> { View.of(xs, 0, 1) }`, called
with `[1, 2]`: a view of a `let` parameter may be returned (views.escaping). -/
def viewKept : VProgram :=
  ⟨noDecls, [("xs", .list .i64, .list [.int 1, .int 2])], .view (.list .i64),
    .viewOf xs (.int 0) (.int 1)⟩

theorem viewKept_wellTyped : viewKept.WellTyped := by
  refine ⟨fun a ha => ?_, .viewOf rfl (.var rfl) .int .int⟩
  simp only [viewKept, List.mem_singleton] at ha
  subst ha
  exact .list (.cons (.int (by decide)) (.cons (.int (by decide)) .nil))

theorem viewKept_accepted : viewKept.Exclusive ∧ viewKept.Contained := by
  unfold VProgram.Exclusive VProgram.Contained
  constructor <;> decide

theorem viewKept_runs :
    viewKept.observe .window 20 = .returned (.list [.int 1]) ∧
      viewKept.observe .copy 20 = .returned (.list [.int 1]) :=
  ⟨rfl, rfl⟩

/-! ## A list changed inside a loop over it -/

/-- `var xs = [1, 2, 3]; for x in xs { xs[0] = x }; xs[0]`. -/
def viewRelisted : VProgram :=
  ⟨noDecls, [], .base .i64, withList
    (.seq (.for "x" .i64 xs (.assign (.index xs (.int 0)) (.var "x"))) (.index xs (.int 0)))⟩

theorem viewRelisted_wellTyped : viewRelisted.WellTyped :=
  ⟨fun _ h => (nomatch h), .varIn viewList_typed
    (.seq (.forList (.var rfl) (.assign (.index (.var rfl) .int) (.var rfl)))
      (.index (.var rfl) .int))⟩

/-- E0404 rejects the change, and E0423 has nothing to reject. -/
theorem viewRelisted_exclusive :
    ¬viewRelisted.Exclusive ∧ viewRelisted.ViewsExclusive ∧ viewRelisted.Contained := by
  unfold VProgram.Exclusive VProgram.ViewsExclusive VProgram.Contained
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Both models agree on it, whatever the fuel: the loop reads the list
itself, so E0404 protects a cost and not the meaning (modes.change-while-iterating). -/
theorem viewRelisted_agrees (fuel : Nat) :
    viewRelisted.observe .window fuel = viewRelisted.observe .copy fuel :=
  viewAgreement_reads viewRelisted fuel viewRelisted_exclusive.2.1 viewRelisted_exclusive.2.2

theorem viewRelisted_runs : viewRelisted.observe .copy 20 = .returned (.int 3) := rfl

end Stilt.Counterexamples
