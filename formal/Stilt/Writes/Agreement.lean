import Stilt.Writes.Places
import Stilt.Writes.Typing

/-!
# Write agreement

The proof of `WriteAgreement`: on a program that obeys the law of exclusivity
with the reads and writes of views (projections.what-view-writes: E0423 and E0429), whose
writable bindings write every source their views have (projections.writable-bindings: E0428), and
whose views don't outlive their sources (views.escaping: E0422), a writable
view as a window, through which a write writes its source's storage at once,
and as a copy of the viewed part, written back into the source when the
binding's scope ends, give the same observation (reference/rationale/13-modes.md,
Writable views). Read-only views are windows and copies too, as in
`Stilt.Views.Agreement`, and a view made from a writable binding is one of
them (projections.places-through-views).

Evaluation keeps the simulation at every fuel, by induction on the fuel, case
by case on the expression.
-/

namespace Stilt.Writes

open Stilt.Views (Store Agree Model)

/-- Evaluation keeps the simulation at every fuel. -/
theorem simulates : ∀ n, Simulates n
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ => trivial
  | n + 1 => fun e Γ R W sw sc hex hco hbd hst hsc => by
    have ih := simulates n
    have hP : ¬(false = true) := Bool.false_ne_true
    cases e <;> simp only [WExpr.exclusive, WExpr.contained, WExpr.bound, Bool.and_eq_true]
      at hex hco hbd
    case var x => exact sim_var hst hsc hex hP
    case int k => exact Post.val hst (Steps.refl _ _) hP
    case list τ es => exact sim_list ih hst hsc hP hex hco hbd
    case index e i => exact sim_index ih hst hsc hP hex.1 hex.2 hco.1 hco.2 hbd.1 hbd.2
    case letIn x τ init body =>
      exact sim_bind (w := false) ih hst hsc hex.1 hex.2 hco.1.1 hco.1.2 hco.2 hbd.1 hbd.2
        fun h => nomatch h
    case varIn x τ init body =>
      exact sim_bind ih hst hsc hex.1 hex.2 hco.1.1 hco.1.2 hco.2 hbd.1.2 hbd.2
        fun h => by simpa [h] using hbd.1.1
    case assign t v =>
      exact sim_assign ih hst hsc hP hex.1.1 hex.1.2 hex.2 hco.1 hco.2 hbd.1 hbd.2
    case seq a b => exact sim_seq ih hst hsc hex.1 hex.2 hco.1 hco.2 hbd.1 hbd.2
    case viewOf src a b =>
      refine sim_make (wr := false) ih hst hsc (fun h => absurd h hP) (fun x hx => ?_)
        hex.1.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2 hbd.1.1 hbd.1.2 hbd.2
      have := hex.1.1.2
      rw [hx] at this
      exact ⟨by simpa [readable] using this, fun h => absurd h hP⟩
    case into src a b =>
      refine sim_make (wr := true) ih hst hsc (fun _ => rfl) (fun x hx => ?_)
        hex.1.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2 hbd.1.1 hbd.1.2 hbd.2
      have := hex.1.1.2
      rw [hx] at this
      simp [modifiable, readable] at this
      exact ⟨this.2, fun _ => this.1⟩
    case sub v a b =>
      exact sim_sub ih hst hsc hP hex.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2 hbd.1.1 hbd.1.2
        hbd.2
    case len v => exact sim_len ih hst hsc hP hex hco hbd

/-! ## Programs -/

/-- The empty states agree. -/
theorem start_agrees :
    StateAgrees ⟨[], []⟩ ⟨[], []⟩ ∧ InScope [] [] [] ([] : List (Name × WBinding)) :=
  ⟨⟨rfl, .nil, fun _ _ => rfl, fun _ _ h => (nomatch h)⟩, ⟨fun _ _ _ h => (nomatch h),
    List.Pairwise.nil, fun _ _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), .nil⟩⟩

/-- Results that agree show the same. -/
theorem shown_agrees {sw sc : Store} {rw rc : WVal} (h : Agrees sw rw rc) :
    shown sw rw = shown sc rc := by
  cases rw <;> cases rc <;> simp only [Agrees] at h
  · subst h
    rfl
  · simp only [shown]
    rw [h]
    rfl
  · simp only [shown]
    rw [h.2.2.2.2]
    rfl

/-- On a body that obeys the law with the reads and writes of views, whose
writable bindings write what their views have as sources, and whose views
don't outlive their sources, the two models give the same observation. -/
theorem WProgram.agree {p : WProgram} (hex : p.Exclusive) (hbd : p.Bound) (hco : p.Contained)
    (fuel : Nat) : p.observe .window fuel = p.observe .copy fuel := by
  obtain ⟨hst, hsc⟩ := start_agrees
  have h := simulates fuel p.body [] [] [] ⟨[], []⟩ ⟨[], []⟩ hex hco hbd hst hsc
  unfold WProgram.observe WProgram.run
  revert h
  cases weval .window fuel p.body ⟨[], []⟩ <;> cases weval .copy fuel p.body ⟨[], []⟩ <;>
    intro h <;> simp only [Agree, Agree.relation, Outcome.Rel] at h <;>
    first | exact h.elim | rfl | (subst h; rfl) | skip
  exact shown_agrees h.agrees

/-! ## Statements -/

/-- **Write agreement**. On a well-typed program that obeys the law of
exclusivity with the reads and writes of views (projections.what-view-writes; views.change-while-viewed; modes.law), whose writable bindings write every source their
views have (projections.writable-bindings), and whose views don't outlive their sources
(views.escaping), a writable view as a window into its source's storage, the
compiler's, and as a copy of the viewed part written back when its binding's
scope ends give the same observation, with the same fuel (reference/rationale/13-modes.md).
`Stilt.Counterexamples.Writes` shows that neither E0429 nor
E0428 can be dropped. -/
def WriteAgreement : Prop :=
  ∀ (p : WProgram) (fuel : Nat), p.WellTyped → p.Exclusive → p.Bound → p.Contained →
    p.observe .window fuel = p.observe .copy fuel

theorem writeAgreement : WriteAgreement :=
  fun _ fuel _ hex hbd hco => WProgram.agree hex hbd hco fuel

end Stilt.Writes
