import Stilt.Views.Loops
import Stilt.Views.Typing

/-!
# View agreement

The proof of `ViewAgreement`: on a program that obeys the law of exclusivity
with the reads of views (views.change-while-viewed), and whose views don't outlive their
sources (views.escaping), a view as a window into its source's storage and a view as
a copy of the viewed part give the same observation. That is the reference interpreter's
justification (reference/rationale/13-modes.md, Views): under views.change-while-viewed nothing can
change a source while a view lives, so a copy can't be told apart from a
window, as copy-in, copy-out can't be told from in-place mutation
(`inPlaceAgreement`).

Evaluation keeps the simulation at every fuel, by induction on the fuel, case
by case on the expression, as `InPlace.eval_agrees` does. The theorem doesn't
need E0404: it holds with the reads of views alone (`viewAgreement_reads`),
since a loop over a list reads the list itself.
-/

namespace Stilt.Views

/-- Evaluation keeps the simulation at every fuel. -/
theorem simulates (D : Decls) (loops : Bool) : ∀ n, Simulates D loops n
  | 0 => fun _ _ _ _ _ _ _ _ _ => trivial
  | n + 1 => fun e Γ R sw sc hex hco hst hsc => by
    have ih := simulates D loops n
    cases e <;> simp only [VExpr.exclusive, VExpr.contained, Bool.and_eq_true] at hex hco
    case var x => exact sim_var hst hsc
    case int k => exact Post.val hst (Steps.refl R sw)
    case bool b => exact Post.val hst (Steps.refl R sw)
    case unit => exact Post.val hst (Steps.refl R sw)
    case record T fs => exact sim_record ih hst hsc hex hco
    case list τ es => exact sim_list ih hst hsc hex hco
    case field e f => exact sim_field ih hst hsc hex hco
    case index e i => exact sim_index ih hst hsc hex.1 hex.2 hco.1 hco.2
    case letIn x τ init body => exact sim_bind ih hst hsc hex.1 hex.2 hco.1.1 hco.1.2 hco.2
    case varIn x τ init body => exact sim_bind ih hst hsc hex.1 hex.2 hco.1.1 hco.1.2 hco.2
    case assign t v => exact sim_assign ih hst hsc hex.1.1 hex.1.2 hex.2 hco.1 hco.2
    case seq a b => exact sim_seq ih hst hsc hex.1 hex.2 hco.1 hco.2
    case «if» c τ a b =>
      exact sim_if ih hst hsc hex.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2
    case «for» x τ it body => exact sim_for ih hst hsc hex.1 hex.2 hco.1 hco.2
    case viewOf src a b =>
      show Agree (Post R src.shape?.toList sw) _ _
      cases hs : src.shape? with
      | some sh =>
        simp only [hs] at hex
        exact sim_make_place ih hst hsc hs hex.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2
      | none =>
        simp only [hs] at hex
        exact sim_make_temp ih hst hsc hs hex.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2
    case sub v a b => exact sim_sub ih hst hsc hex.1.1 hex.1.2 hex.2 hco.1.1 hco.1.2 hco.2
    case len v => exact sim_len ih hst hsc hex hco
    case copy v => exact sim_copy ih hst hsc hex hco

/-! ## Programs -/

theorem frame_loc {x : Name} {b : Binding} :
    ∀ {names : List Name} {i : Nat}, (x, b) ∈ frame names i →
      ∃ ℓ, b = .loc ℓ ∧ i ≤ ℓ ∧ ℓ < i + names.length
  | [], _, h => by cases h
  | y :: names, i, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
      exact ⟨i, rfl, Nat.le_refl _, by simp⟩
    · obtain ⟨ℓ, rfl, h₁, h₂⟩ := frame_loc h
      exact ⟨ℓ, rfl, by omega, by simp only [List.length_cons]; omega⟩

theorem frame_distinct {x y : Name} {ℓ : Nat} :
    ∀ {names : List Name} {i : Nat}, (x, Binding.loc ℓ) ∈ frame names i →
      (y, Binding.loc ℓ) ∈ frame names i → x = y
  | [], _, h, _ => by cases h
  | z :: names, i, hx, hy => by
    rcases List.mem_cons.1 hx with hx | hx <;> rcases List.mem_cons.1 hy with hy | hy
    · simp only [Prod.mk.injEq] at hx hy
      exact hx.1.trans hy.1.symm
    · simp only [Prod.mk.injEq, Binding.loc.injEq] at hx
      obtain ⟨_, he, h₁, -⟩ := frame_loc hy
      simp only [Binding.loc.injEq] at he
      omega
    · simp only [Prod.mk.injEq, Binding.loc.injEq] at hy
      obtain ⟨_, he, h₁, -⟩ := frame_loc hx
      simp only [Binding.loc.injEq] at he
      omega
    · exact frame_distinct hx hy

theorem frame_agrees (store : Store) :
    ∀ (names : List Name) (i : Nat), EnvAgrees store (frame names i) (frame names i)
  | [], _ => .nil
  | _ :: names, i => .cons ⟨rfl, rfl⟩ (frame_agrees store names (i + 1))

theorem frame_sources {env : List (Name × Binding)} :
    ∀ (names : List Name) (i : Nat),
      Pointwise (fun (g : Name × List Shape) (e : Name × Binding) =>
        g.1 = e.1 ∧ ∀ ℓ π a b, e.2 = .view (.window ℓ π a b) → Covered g.2 env ℓ π)
        (names.map fun x => (x, [])) (frame names i)
  | [], _ => .nil
  | _ :: names, i => .cons ⟨rfl, fun _ _ _ _ h => nomatch h⟩ (frame_sources names (i + 1))

/-- The state a body starts in agrees with itself, and holds no view. -/
theorem VProgram.start_agrees (p : VProgram) :
    StateAgrees p.start p.start ∧ InScope p.sources [] p.start.env := by
  refine ⟨⟨rfl, frame_agrees _ _ 0, fun x ℓ hx => ?_⟩, ⟨fun x y ℓ hx hy => frame_distinct hx hy,
    fun x ℓ π a b hx => ?_, ?_⟩⟩
  · obtain ⟨ℓ', he, -, hlt⟩ := frame_loc hx
    cases he
    simpa [VProgram.start] using hlt
  · obtain ⟨_, he, -⟩ := frame_loc hx
    exact nomatch he
  · have := frame_sources (env := p.start.env) (p.args.map (·.1)) 0
    simpa [VProgram.sources, VProgram.start, List.map_map, Function.comp_def] using this

/-- Results that agree show the same. -/
theorem shown_agrees {store : Store} {rw rc : RVal} (h : Agrees store rw rc) :
    shown store rw = shown store rc := by
  cases rw <;> cases rc <;> try exact False.elim h
  · cases (show _ = _ from h)
    rfl
  · simp only [shown]
    rw [show (RVal.window _ _ _ _).part store = _ from h]
    rfl

/-- On a body that obeys the law with the reads of views, whatever `loops`
says of E0404, and whose views don't outlive their sources, the two models of
a view give the same observation. -/
theorem VProgram.agree {p : VProgram} {loops : Bool}
    (hex : p.body.exclusive loops p.sources [] = true) (hco : p.body.contained p.sources = true)
    (fuel : Nat) : p.observe .window fuel = p.observe .copy fuel := by
  obtain ⟨hst, hsc⟩ := p.start_agrees
  have h := simulates p.decls loops fuel p.body p.sources [] p.start p.start hex hco hst hsc
  unfold VProgram.observe VProgram.run
  revert h
  cases veval p.decls .window fuel p.body p.start <;>
    cases veval p.decls .copy fuel p.body p.start <;> intro h <;>
    simp only [Agree, Agree.relation, Outcome.Rel] at h <;>
    first | exact h.elim | rfl | (subst h; rfl) | skip
  rename_i rw sw rc sc
  show shown sw.store rw = shown sc.store rc
  rw [← h.states.store]
  exact shown_agrees h.agrees

/-! ## Statements -/

/-- **View agreement**. On a well-typed program that obeys the law of
exclusivity with the reads of views (views.reads-that-last and views.change-while-viewed; modes.law),
and whose views don't outlive their sources (views.escaping), a view as a window into
its source's storage, the compiler's, and as a copy of the viewed part, the
reference interpreter's, give the same observation, with the same fuel (reference/rationale/13-modes.md).
`Stilt.Counterexamples.Views` shows that neither E0423 nor
E0422 can be dropped. -/
def ViewAgreement : Prop :=
  ∀ (p : VProgram) (fuel : Nat), p.WellTyped → p.Exclusive → p.Contained →
    p.observe .window fuel = p.observe .copy fuel

theorem viewAgreement : ViewAgreement :=
  fun _ fuel _ hex hco => VProgram.agree hex hco fuel

/-- The agreement needs neither typing nor E0404: the reads of views alone,
which E0423 protects, and views.escaping. -/
theorem viewAgreement_reads (p : VProgram) (fuel : Nat) (hex : p.ViewsExclusive)
    (hco : p.Contained) : p.observe .window fuel = p.observe .copy fuel :=
  VProgram.agree hex hco fuel

end Stilt.Views
