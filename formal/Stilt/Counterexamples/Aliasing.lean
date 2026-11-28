import Stilt.Exclusivity
import Stilt.Semantics
import Stilt.Counterexamples.Checks

/-!
# Overlapping `inout` arguments

A program that shows that `InPlaceAgreement` needs exclusivity: a well-typed
call with two overlapping `inout` arguments, which modes.overlapping-inout rejects,
tells copy-in, copy-out from in-place mutation. `main` returns `()` (program.main), so it raises the call's result, and the two runs raise different
values.
-/

namespace Stilt.Counterexamples

/-- `fn alias(inout x: i64, inout y: i64) -> i64 { x = 1; y }`. -/
def alias : FnDecl :=
  ⟨"alias", [], [], [⟨.inout, "x", .i64, none⟩, ⟨.inout, "y", .i64, none⟩], .i64, Row.pure,
    .seq (.assign ⟨"x", []⟩ (.int 1)) (.var "y"), {}⟩

/-- `var a = 0; raise alias(inout a, inout a)`, in a `main` whose row is
`raise<i64>`. modes.overlapping-inout rejects the call. -/
def aliased : Program :=
  ⟨⟨[], [], [alias], [], [], [], [], []⟩,
    .varIn "a" .i64 (.int 0)
      (.raise (.call (.fnRef "alias" [] []) [.inout ⟨"a", []⟩, .inout ⟨"a", []⟩] .i64)),
    ⟨false, some .i64, [], [], none⟩, {}, {}⟩

theorem aliased_wellTyped : aliased.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by simp [aliased]) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [aliased, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact ⟨.i64, .seq (.assign (.mk rfl .nil) (.int (by decide)) (.refl _)) (.refl _) (.var rfl), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hcallee :
        HasType aliased.decls .closed [("a", ⟨.i64, true⟩)] ⟨aliased.row, false, false, .unit, false, false⟩
        (.fnRef "alias" [] []) (alias.type.substRows (alias.rowParams.zip [])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
        (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .varIn (wellFormed_of_check (by decide)) (.int (by decide)) (.refl _)
      (.raise rfl (.call hcallee (.inout (.mk rfl .nil) (.inout (.mk rfl .nil) .nil))
        ⟨Row.pure_within _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩) (.refl _)), .never _⟩
  noEscape := noEscape_of_check (by decide)

/-- The law of exclusivity rejects the call. -/
theorem aliased_not_exclusive : ¬aliased.Exclusive := by
  rintro ⟨_, h⟩
  exact absurd h (by decide)

/-- Copy-in, copy-out gives `y` the value `a` had when the call started, and
writes back `x`, then `y`, so `main` raises 0. In place, `x` and `y` are both
`a`, so `main` raises 1. -/
theorem aliased_runs :
    (aliased.runCopy 16).observe = .raised (.int 0) ∧
      (aliased.runInPlace 16).observe = .raised (.int 1) :=
  ⟨rfl, rfl⟩

/-- `InPlaceAgreement` needs exclusivity: without it, a well-typed program
tells the two models apart. -/
theorem exclusivity_needed :
    ¬∀ (p : Program) (fuel : Nat), p.WellTyped →
      (p.runCopy fuel).observe = (p.runInPlace fuel).observe := by
  intro h
  have hagree := h aliased 16 aliased_wellTyped
  rw [aliased_runs.1, aliased_runs.2] at hagree
  exact nomatch hagree

end Stilt.Counterexamples
