import Stilt.Writes.Agreement

/-!
# Views that write what someone else reaches

Programs that show what `WriteAgreement` needs, as
`Stilt.Counterexamples.Views` does for `ViewAgreement`. Each is well typed,
and breaks one rule of projections.reaching-written-source and projections.writable-bindings:

* `writeReached` views `xs` while a writable binding writes it, which projections.reaching-written-source
  rejects (E0429): the write through `v` reaches the value that `w`, bound by
  `let`, holds, so `w[0]` changes after its binding. So E0429 is a soundness
  rule (values.value-semantics; projections.reaching-written-source);
* `writeViewed` writes through `v` while a view made from it lives, which
  projections.places-through-views rejects (E0423);
* `writeLost` gives a `var` binding a view that reads `xs`, which projections.writable-bindings
  rejects (E0428): the window writes `xs`, the copy writes nothing back.

`writeShared` binds `ys` to `xs` before the view is made, which the rules
accept: both models leave `ys` as it was (projections.writable-views).
-/

namespace Stilt.Counterexamples

open Stilt.Views (VTy)
open Stilt.Writes

/-- The type of a view of a list of `i64`. -/
private def viewTy : VTy := .view (.list .i64)

/-- `var xs = [1, 2, 3]`, followed by `rest`. -/
private def withList (rest : WExpr) : WExpr :=
  .varIn "xs" (.base (.list .i64)) (.list .i64 [.int 1, .int 2, .int 3]) rest

/-- `var v = view.into(inout xs, 0, 3)`, followed by `rest`. -/
private def withInto (rest : WExpr) : WExpr :=
  .varIn "v" viewTy (.into (.var "xs") (.int 0) (.int 3)) rest

/-- `v[0] = 9`, followed by `rest`. -/
private def written (rest : WExpr) : WExpr :=
  .seq (.assign (.index (.var "v") (.int 0)) (.int 9)) rest

theorem list_typed {Γ : Writes.Ctx} :
    HasType Γ (.list .i64 [.int 1, .int 2, .int 3]) (.base (.list .i64)) :=
  .list fun e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact .int

/-- The law of exclusivity without E0429, which keeps E0423. -/
private def lawful (p : WProgram) : Prop := p.body.exclusive false [] [] [] = true

/-! ## A value bound by `let` that a write reaches -/

/-- `var xs = [1, 2, 3]; var v = view.into(inout xs, 0, 3);
let w = View.of(xs, 0, 3); v[0] = 9; w[0]`. -/
def writeReached : WProgram :=
  ⟨.base .i64, withList (withInto (.letIn "w" viewTy (.viewOf (.var "xs") (.int 0) (.int 3))
    (written (.index (.var "w") (.int 0)))))⟩

theorem writeReached_wellTyped : writeReached.WellTyped :=
  .varIn list_typed (.varIn (.into (.var rfl) .int .int) (.letIn (.viewOf rfl rfl (.var rfl) .int .int)
    (.seq (.assignThrough rfl .int .int) (.viewIndex (.var rfl) .int))))

/-- E0429 rejects the view of `xs`, and nothing else rejects the program. -/
theorem writeReached_checks : ¬writeReached.Exclusive ∧ lawful writeReached ∧
    writeReached.Bound ∧ writeReached.Contained := by
  unfold WProgram.Exclusive lawful WProgram.Bound WProgram.Contained
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The window reads the write through `v`; the copy, written back only when
`v`'s scope ends, doesn't. -/
theorem writeReached_runs :
    writeReached.observe .window 30 = .returned (.int 9) ∧
      writeReached.observe .copy 30 = .returned (.int 1) :=
  ⟨rfl, rfl⟩

/-- `WriteAgreement` needs E0429: without it, a well-typed program that obeys
E0423, E0428 and E0422 tells the two models apart. -/
theorem writeLocks_needed :
    ¬∀ (p : WProgram) (fuel : Nat), p.WellTyped → lawful p → p.Bound → p.Contained →
      p.observe .window fuel = p.observe .copy fuel := by
  intro h
  have hagree := h writeReached 30 writeReached_wellTyped writeReached_checks.2.1
    writeReached_checks.2.2.1 writeReached_checks.2.2.2
  rw [writeReached_runs.1, writeReached_runs.2] at hagree
  exact nomatch hagree

/-- A read of the source while `v` writes it: `v[0] = 9; xs[0]` reads 9 through
the window and 1 from the copy's source. -/
theorem writeRead_runs :
    (⟨.base .i64, withList (withInto (written (.index (.var "xs") (.int 0))))⟩ : WProgram).observe
        .window 30 = .returned (.int 9) ∧
      (⟨.base .i64, withList (withInto (written (.index (.var "xs") (.int 0))))⟩ : WProgram).observe
        .copy 30 = .returned (.int 1) :=
  ⟨rfl, rfl⟩

/-! ## A writable binding changed under a view of it -/

/-- `var xs = [1, 2, 3]; var v = view.into(inout xs, 0, 3); let w = v.view(0, 2);
v[0] = 9; w[0]`. -/
def writeViewed : WProgram :=
  ⟨.base .i64, withList (withInto (.letIn "w" viewTy (.sub (.var "v") (.int 0) (.int 2))
    (written (.index (.var "w") (.int 0)))))⟩

/-- E0423 rejects the write through `v`, whose view `w` reads it (projections.places-through-views), with E0429 or without it. -/
theorem writeViewed_checks : ¬writeViewed.Exclusive ∧ ¬lawful writeViewed := by
  unfold WProgram.Exclusive lawful
  constructor <;> decide

theorem writeViewed_runs :
    writeViewed.observe .window 30 = .returned (.int 9) ∧
      writeViewed.observe .copy 30 = .returned (.int 1) :=
  ⟨rfl, rfl⟩

/-! ## A writable binding given a view that reads -/

/-- `var xs = [1, 2, 3]; { var v = View.of(xs, 0, 3); v[0] = 9 }; xs[0]`. -/
def writeLost : WProgram :=
  ⟨.base .i64, withList (.seq (.varIn "v" viewTy (.viewOf (.var "xs") (.int 0) (.int 3))
    (.assign (.index (.var "v") (.int 0)) (.int 9))) (.index (.var "xs") (.int 0)))⟩

theorem writeLost_wellTyped : writeLost.WellTyped :=
  .varIn list_typed (.seq (.varIn (.viewOf rfl rfl (.var rfl) .int .int)
    (.assignThrough rfl .int .int)) (.index (.var rfl) .int))

/-- E0428 rejects the binding, and nothing else rejects the program. -/
theorem writeLost_checks :
    ¬writeLost.Bound ∧ writeLost.Exclusive ∧ writeLost.Contained := by
  unfold WProgram.Bound WProgram.Exclusive WProgram.Contained
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The window writes `xs`, and the copy, which `View.of` made, has no place
to write back to. -/
theorem writeLost_runs :
    writeLost.observe .window 30 = .returned (.int 9) ∧
      writeLost.observe .copy 30 = .returned (.int 1) :=
  ⟨rfl, rfl⟩

/-- `WriteAgreement` needs E0428. -/
theorem bound_needed :
    ¬∀ (p : WProgram) (fuel : Nat), p.WellTyped → p.Exclusive → p.Contained →
      p.observe .window fuel = p.observe .copy fuel := by
  intro h
  have hagree := h writeLost 30 writeLost_wellTyped writeLost_checks.2.1 writeLost_checks.2.2
  rw [writeLost_runs.1, writeLost_runs.2] at hagree
  exact nomatch hagree

/-! ## A list bound before its view is made -/

/-- `var xs = [1, 2, 3]; let ys = xs; var v = view.into(inout xs, 0, 3);
v[0] = 9; ys[0]`. -/
def writeShared : WProgram :=
  ⟨.base .i64, withList (.letIn "ys" (.base (.list .i64)) (.var "xs")
    (withInto (written (.index (.var "ys") (.int 0)))))⟩

theorem writeShared_accepted :
    writeShared.Exclusive ∧ writeShared.Bound ∧ writeShared.Contained := by
  unfold WProgram.Exclusive WProgram.Bound WProgram.Contained
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `ys` keeps the value it was bound to in both models. -/
theorem writeShared_runs :
    writeShared.observe .window 30 = .returned (.int 1) ∧
      writeShared.observe .copy 30 = .returned (.int 1) :=
  ⟨rfl, rfl⟩

end Stilt.Counterexamples
