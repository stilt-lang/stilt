import Stilt.Writes.Cases

/-!
# Places

The cases of the simulation that evaluate a place: an assignment, which
writes a variable or writes through a writable binding where nothing reads or
writes it (views.change-while-viewed; projections.what-view-writes and projections.places-through-views), and `View.of` and
`view.into`, whose window reads the place it was made from (views.making-view;
projections.writable-views). A place's indexes are evaluated in both models alike, and its
root is the one the static analysis compares.
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree Agree Model)

variable {n : Nat}

theorem StateAgrees.loc {sw sc : WState} (h : StateAgrees sw sc) (x : Name) :
    sw.loc? x = sc.loc? x := by
  unfold WState.loc?
  rcases h.env.lookup x with ⟨h₁, h₂⟩ | ⟨b, c, h₁, h₂, hbc⟩
  · rw [h₁, h₂]
  rw [h₁, h₂]
  cases b with
  | loc ℓ =>
    cases c <;> simp only [BAgrees] at hbc
    rw [hbc]
  | view r =>
    obtain ⟨r', rfl, -⟩ := hbc.view_inv
    rfl
  | writes r =>
    obtain ⟨_, _, _, _, _, rfl, rfl, -⟩ := hbc.writes_inv
    rfl

theorem loc?_lookup {s : WState} {x : Name} {ℓ : Nat} (h : s.loc? x = .ok ℓ) :
    s.env.lookup x = some (.loc ℓ) := by
  unfold WState.loc? at h
  split at h
  · cases h
    assumption
  · cases h

/-- A place, evaluated in both models: the same root and path. -/
theorem Simulates.place (ih : Simulates n) {Γ : Sources} {R W : List Name} :
    ∀ (t : WExpr) {sw sc : WState}, t.placeExclusive true Γ R W = true →
      t.contained Γ = true → t.bound = true → StateAgrees sw sc → InScope Γ R W sw.env →
      Agree (fun s sc' (p q : Name × Path) =>
          p = q ∧ t.root? = some p.1 ∧ StateAgrees s sc' ∧ Steps (R ++ W) sw s)
        (Run.place (weval .window n) t sw) (Run.place (weval .copy n) t sc)
  | .var _, _, _, _, _, _, hst, _ => ⟨rfl, rfl, hst, Steps.refl _ _⟩
  | .index e i, _, _, hex, hco, hbd, hst, hsc => by
    simp only [WExpr.placeExclusive, WExpr.contained, WExpr.bound, Bool.and_eq_true]
      at hex hco hbd
    refine Agree.bind (Simulates.place ih e hex.1 hco.1 hbd.1 hst hsc)
      fun s₁ sc₁ p q ⟨hpq, hr, hst₁, hs₁⟩ => ?_
    subst hpq
    refine Agree.bind (ih.int hex.2 hco.2 hbd.2 hst₁ (hsc.after hs₁)) fun s₂ sc₂ k k' ho => ?_
    cases ho.eq
    exact ⟨rfl, hr, ho.states, hs₁.trans ho.steps fun _ h => h⟩
  | .int _, _, _, _, _, _, _, _ | .list _ _, _, _, _, _, _, _, _
  | .letIn _ _ _ _, _, _, _, _, _, _, _ | .varIn _ _ _ _, _, _, _, _, _, _, _
  | .assign _ _, _, _, _, _, _, _, _ | .seq _ _, _, _, _, _, _, _, _
  | .viewOf _ _ _, _, _, _, _, _, _, _ | .into _ _ _, _, _, _, _, _, _, _
  | .sub _ _ _, _, _, _, _, _, _, _ | .len _, _, _, _, _, _, _, _ => Agree.stuck

/-- A write to a place whose root nothing reads or writes: a variable, or `v[k]`
through a writable binding (projections.places-through-views). -/
theorem StateAgrees.write {Γ : Sources} {R W : List Name} {sw sc : WState}
    (h : StateAgrees sw sc) (hs : InScope Γ R W sw.env) {x : Name} {π : Path} {w : Value}
    (hF : x ∉ R ++ W) :
    ExceptAgree (fun sw' sc' => StateAgrees sw' sc' ∧ Steps (R ++ W) sw sw')
      (sw.write x π w) (sc.write x π w) := by
  unfold WState.write
  rcases h.env.lookup x with ⟨h₁, h₂⟩ | ⟨b, c, h₁, h₂, hbc⟩
  · rw [h₁, h₂]
    exact rfl
  rw [h₁, h₂]
  cases b with
  | loc ℓ =>
    cases c <;> simp only [BAgrees] at hbc
    subst hbc
    have := h.setLoc hs h₁ hF (π := π) (w := w)
    revert this
    dsimp only
    cases setCell sw.store ℓ π w <;> cases setCell sc.store ℓ π w <;> intro this <;>
      simp only [ExceptAgree] at this ⊢ <;> first | exact this | exact this.elim
  | view r =>
    obtain ⟨r', rfl, -⟩ := hbc.view_inv
    exact rfl
  | writes r =>
    obtain ⟨ℓ, π', a, b, part, rfl, rfl, hr⟩ := hbc.writes_inv
    rcases π with _ | ⟨_ | k, _ | ⟨_, _⟩⟩
    all_goals first | exact rfl | exact h.through hs h₁ hr hF

section Places

variable (ih : Simulates n) {Γ : Sources} {R W S : List Name} {P : Prop} {sw sc : WState}
  (hst : StateAgrees sw sc) (hsc : InScope Γ R W sw.env)
include ih hst hsc

/-- An assignment writes a place whose root nothing reads or writes (E0423 and
E0429). -/
theorem sim_assign {t v : WExpr} (hP : ¬P) (ht : t.placeExclusive true Γ R W = true)
    (hv : v.exclusive true Γ R W = true) (hu : t.root?.all (modifiable true R W) = true)
    (hct : t.contained Γ = true) (hcv : v.contained Γ = true) (hbt : t.bound = true)
    (hbv : v.bound = true) :
    Agree (Post (R ++ W) S P sw) (Run.assign (weval .window n) t v sw)
      (Run.assign (weval .copy n) t v sc) := by
  refine Agree.bind (ih.place t ht hct hbt hst hsc) fun s₁ sc₁ p q ⟨hpq, hr, hst₁, hs₁⟩ => ?_
  subst hpq
  refine Agree.bind (ih.value hv hcv hbv hst₁ (hsc.after hs₁)) fun s₂ sc₂ w w' ho => ?_
  cases ho.eq
  have hF : p.1 ∉ R ++ W := by
    rw [hr] at hu
    simpa [modifiable, readable] using hu
  have hs₂ := hs₁.trans ho.steps fun _ h => h
  refine Agree.bind (Agree.update (Q := fun s sc' _ _ => StateAgrees s sc' ∧ Steps (R ++ W) s₂ s)
    (ho.states.write (hsc.after hs₂) hF)) fun s₃ sc₃ _ _ ⟨hst₃, hs₃⟩ => ?_
  exact Post.val hst₃ (hs₂.trans hs₃ fun _ h => h) hP

/-- `View.of(x[…], a, b)` and `view.into(inout x[…], a, b)`: a window into the
place, whose root is its source, of a variable that no writable binding locks
(E0429), and that no view reads for `view.into` (E0423). -/
theorem sim_make {wr : Bool} {src a b : WExpr} (hP : P → wr = true)
    (hx : ∀ x, src.root? = some x → x ∉ W ∧ (wr = true → x ∉ R))
    (hp : src.placeExclusive true Γ R W = true) (ha : a.exclusive true Γ R W = true)
    (hb : b.exclusive true Γ R W = true) (hcs : src.contained Γ = true)
    (hca : a.contained Γ = true) (hcb : b.contained Γ = true) (hbs : src.bound = true)
    (hba : a.bound = true) (hbb : b.bound = true) :
    Agree (Post (R ++ W) src.root?.toList P sw) (Run.make .window wr (weval .window n) src a b sw)
      (Run.make .copy wr (weval .copy n) src a b sc) := by
  unfold Run.make
  refine Agree.bind (ih.place src hp hcs hbs hst hsc) fun s₁ sc₁ p q ⟨hpq, hr, hst₁, hs₁⟩ => ?_
  subst hpq
  refine Agree.bind (ih.int ha hca hba hst₁ (hsc.after hs₁)) fun s₂ sc₂ x x' ho₂ => ?_
  have hs₂ := hs₁.trans ho₂.steps fun _ h => h
  refine Agree.bind (ih.int hb hcb hbb ho₂.states (hsc.after hs₂)) fun s₃ sc₃ y y' ho₃ => ?_
  cases ho₂.eq
  cases ho₃.eq
  have hs₃ := hs₂.trans ho₃.steps fun _ h => h
  have hsc₃ := hsc.after hs₃
  obtain ⟨hW, hR⟩ := hx p.1 hr
  refine Agree.inspect ?_
  rw [← ho₃.states.loc p.1]
  cases hl : s₃.loc? p.1 with
  | error f => exact rfl
  | ok ℓ =>
    have hlk := loc?_lookup hl
    refine Views.ExceptAgree.mono (ho₃.states.make hsc₃ hlk hW wr p.2 x y)
      fun rw rc _ ⟨hag, hw, hpd⟩ => ⟨ho₃.states, hs₃, hag, fun ℓ' π c d he => ?_, fun hP' => ?_⟩
    · rw [hw] at he
      cases he
      rw [hr, ← hs₃.env]
      exact hsc₃.cover_root hlk hW
    · have hF : p.1 ∉ R ++ W := by
        simpa [hW] using hR (hP hP')
      obtain ⟨part, rfl⟩ := hpd (hP hP')
      exact ⟨part, ℓ, p.2, x, y, hw, rfl, hs₃.env ▸ hsc₃.alone_root hlk hF, p.1, hs₃.env ▸ hlk, hF⟩

end Places

end Stilt.Writes
